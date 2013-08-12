{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Sparse.Matrix where

import Control.Applicative
import Control.Lens
import Control.Monad.Primitive
import Data.Bits
import Data.Bits.Extras
import Data.Foldable
import Data.Function (on)
import qualified Data.Vector.Algorithms.Intro as Intro
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Hybrid as H
import qualified Data.Vector.Hybrid.Internal as H
import Data.Vector.Fusion.Stream as S (Stream, fromList, filter)
import qualified Data.Vector.Unboxed as U
import Data.Word
import Sparse.Key
import Sparse.Fusion

-- * Sparse Matrices

class Eq0 a where
  isZero :: a -> Bool
#ifndef HLINT
  default isZero :: (Num a, Eq a) => a -> Bool
  isZero = (0 ==)
  {-# INLINE isZero #-}
#endif

instance Eq0 Int
instance Eq0 Word
instance Eq0 Integer
instance Eq0 Float
instance Eq0 Double

newtype Mat v a = Mat { runMat :: H.Vector U.Vector v (Key, a) } deriving (Show)

_Mat :: Iso (Mat u a) (Mat v b) (H.Vector U.Vector u (Key, a)) (H.Vector U.Vector v (Key, b))
_Mat = iso runMat Mat

keys :: Lens (H.Vector u v (a,b)) (H.Vector w v (c,b)) (u a) (w c)
keys f (H.V ks vs) = f ks <&> \ks' -> H.V ks' vs

values :: Lens (H.Vector u v (a,b)) (H.Vector u w (a,c)) (v b) (w c)
values f (H.V ks vs) = f vs <&> \vs' -> H.V ks vs'

instance Functor v => Functor (Mat v) where
  fmap = over (_Mat.values.mapped)
  {-# INLINE fmap #-}

instance Foldable v => Foldable (Mat v) where
  foldMap = foldMapOf (_Mat.values.folded)
  {-# INLINE foldMap #-}

instance Traversable v => Traversable (Mat v) where
  traverse = _Mat.values.traverse
  {-# INLINE traverse #-}

type instance IxValue (Mat v a) = a
type instance Index (Mat v a) = Key

-- only legal for top level matrices or where the singleton value matches on all of the bits of the 'context'
instance (Applicative f, G.Vector v a) => Ixed f (Mat v a) where
  ix i f m@(Mat (H.V ks vs))
    | Just j <- ks U.!? l, i == j = indexed f i (vs G.! l) <&> \v -> Mat (H.V ks (vs G.// [(l,v)]))
    | otherwise                   = pure m
    where l = search (\j -> (ks U.! j) >= i) 0 (U.length ks)
  {-# INLINE ix #-}

-- only legal for top level matrices or where the singleton value matches on all of the bits of the 'context'
instance G.Vector v a => At (Mat v a) where
  at i f m@(Mat (H.V ks vs)) = case ks U.!? l of
    Just j
      | i == j -> indexed f i (Just (vs G.! l)) <&> \mv -> case mv of
        Just v  -> Mat $ H.V ks (vs G.// [(l,v)])
        Nothing  -> undefined -- TODO: delete
    _ -> indexed f i Nothing <&> \mv -> case mv of
        Just _v -> undefined -- TODO: insert v
        Nothing -> m
    where l = search (\j -> (ks U.! j) >= i) 0 (U.length ks)
  {-# INLINE at #-}

instance Eq0 (Mat v a) where
  isZero = H.null . runMat
  {-# INLINE isZero #-}

-- Build a sparse (h * w) a-valued matrix.
fromStream :: G.Vector v a => Stream (Key, a) -> Mat v a
fromStream xs = Mat $ H.modify (Intro.sortBy (compare `on` fst)) $ G.unstream xs
{-# INLINE fromStream #-}

fromList :: G.Vector v a => [(Key, a)] -> Mat v a
fromList = fromStream . S.fromList
{-# INLINE fromList #-}

singleton :: G.Vector v a => Key -> a -> Mat v a
singleton k v = Mat $ H.singleton (k,v)
{-# INLINE singleton #-}

count :: Mat v a -> Int
count = H.length . runMat
{-# INLINE count #-}

empty :: G.Vector v a => Mat v a
empty = Mat H.empty
{-# INLINE empty #-}

ident :: (G.Vector v a, Num a) => Word32 -> Mat v a
ident w = Mat $ H.generate (fromIntegral w) $ \i -> let i' = fromIntegral i in (key i' i', 1)
{-# INLINE ident #-}

{-
-- | partition (and rejoin) along the major axis into a 2-fat component and the remainder.
--
-- Note: the keys have 'junk' on the top of the keys, but it should be exactly the junk we need them to have when we rejoin the quadrants
--       or reassemble a key from matrix multiplication.
--
-- @mlzs@ gives you enough information to be able to trim them otherwise.

split :: G.Vector v a => IndexedTraversal' (Bool, Int) (Mat v a) (Mat v a, Mat v a)
split f m@(Mat mask body@(H.V ks _))
  | n < 2     = pure m
  | otherwise = f (m0,m1) <&> \ (Mat _ u,Mat _ v) -> Mat mask (u ++ v)
  where
    lo = head ks
    hi = last ks
    xor lo hi


quadrants :: G.Vector v a => Lens' (Mat v a) (Mat v a, Mat v a, Mat v a, Mat v a)
quadrants f (Mat lzs body@(H.V ks _)) =
  f ( m00, m01, m10, m11) <&> \ (m00', m01', m10', m11') -> Mat lzs i0 j0 h w $
      G.unstream $ concatFour (G.stream (_matBody m00')) (G.stream (_matBody m01')) (G.stream (_matBody m10')) (G.stream (_matBody m11'))
  where
    hmask = bit (64 - 2*lzs)
    lmask = unsafeShiftR hmask 1
    n = U.length ks
    split2 = search (\i -> rawKey (ks U.! i) .&. hmask /= 0) 0 n
    split1 = search (\i -> rawKey (ks U.! i) .&. lmask /= 0) 0 split2
    split3 = search (\i -> rawKey (ks U.! i) .&. lmask /= 0) split2 n
    (uh,lh)   = H.splitAt split1 body
    (b00,b01) = H.splitAt split1 uh
    (b10,b11) = H.splitAt (split3 - split2) lh
    m00 = Mat lzs' i0      j0      dh     dw     b00
    m01 = Mat lzs' i0      (j0+dw) dh     (w-dw) b01
    m10 = Mat lzs' (i0+dh) j0      (h-dh) dw     b10
    m11 = Mat lzs' (i0+dh) (j0+dh) (h-dw) (w-dw) b11
    dh = fattest h
    dw = fattest w
    lzs' = lzs + 1

-- (i x j, j x k) -> (i x k)

{-
multiply :: G.Vector v a => Mat v a -> Mat v a -> Mat v a
multiply x y
  | isZero x || isZero y = zero h w
  | count x == 1 -- each side has a single entry, so we might as well solve for it!
  , count y == 1
  , (ij,xij) <- H.head (matBody x)
  , (jk,yjk) <- H.head (matBody y) = if ij^._jj == jk^._ii then singleton h w (jk&_1.~ij^._1) (xij*yjk) else zero h w
  | (x00,x01,x10,x11) <- quadrants x
  , (y00,y01,y11,y11) <- quadrants y
  where
        h = height x
        w = width y
-}


-- * Utilities

-- |
-- @fattest x@ is the nearest power of two that is less than x@
--
-- This is called the \"2-fattest\" integer in the range [1..x).
--
-- The 2-fattest number in (a..b] is @shiftL (-1) (msb (xor a b)) .&. b@.
fattest :: Word32 -> Word32
fattest y0 = unsafeShiftR x5 1 + 1 where
  x0 = y0 - 1
  x1 = x0 .|. unsafeShiftR x0 1
  x2 = x1 .|. unsafeShiftR x1 2
  x3 = x2 .|. unsafeShiftR x2 4
  x4 = x3 .|. unsafeShiftR x3 8
  x5 = x4 .|. unsafeShiftR x4 16
{-# INLINE fattest #-}
-}

-- | assuming @l <= h@. Returns @h@ if the predicate is never @True@ over @[l..h)@
search :: (Int -> Bool) -> Int -> Int -> Int
search p = go where
  go l h
    | l == h    = l
    | p m       = go l m
    | otherwise = go (m+1) h
    where m = l + div (h-l) 2
{-# INLINE search #-}

{-
{-
mergeMatricesWith :: (a -> a -> Maybe a) -> Mat v a -> Mat v a -> Mat v a
mergeMatricesWith = undefined
-- mergeMatricesWith f (Mat 
-}

plus :: (Num a, Eq a) => a -> a -> Maybe a
plus a b = case a + b of
  c | c == 0    -> Nothing
    | otherwise -> Just c
{-# INLINE plus #-}

-- used for vector addition
mergeVectorsWith :: (G.Vector v (i, a), Ord i) => (a -> a -> Maybe a) -> v (i, a) -> v (i, a) -> v (i, a)
mergeVectorsWith f va vb = G.unstream (mergeStreamsWith f (G.stream va) (G.stream vb))
{-# INLINE mergeVectorsWith #-}

-- Given a sorted array in [l,u), inserts val into its proper position,
-- yielding a sorted [l,u]
insert :: (PrimMonad m, GM.MVector v e) => (e -> e -> Ordering) -> v (PrimState m) e -> Int -> e -> Int -> m ()
insert cmp a l = loop
 where
 loop val j
   | j <= l    = GM.unsafeWrite a l val
   | otherwise = do e <- GM.unsafeRead a (j - 1)
                    case cmp val e of
                      LT -> GM.unsafeWrite a j e >> loop val (j - 1)
                      _  -> GM.unsafeWrite a j val
{-# INLINE insert #-}
-}
