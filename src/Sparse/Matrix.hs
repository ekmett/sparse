{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Sparse.Matrix where

import Control.Applicative
import Control.Lens
import Control.Monad.Primitive
import Data.Bits
import Data.Bits.Extras
import Data.Foldable
import Data.Function (on)
import qualified Data.Vector.Algorithms.Intro as Intro
-- import qualified Data.Vector as B
import Data.Vector.Fusion.Stream.Monadic (Step(..), Stream(..))
import Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Hybrid as H
import qualified Data.Vector.Hybrid.Internal as H
-- import qualified Data.Vector.Primitive as P
import qualified Data.Vector.Unboxed as U
-- import qualified Data.Vector.Unboxed.Mutable as UM
import Data.Word
import Sparse.Key
-- import Debug.Trace

-- * Sparse Matrices

class Eq0 a where
  isZero :: a -> Bool
  default isZero :: (Num a, Eq a) => a -> Bool
  isZero = (0 ==)
  {-# INLINE isZero #-}

instance Eq0 Int
instance Eq0 Word
instance Eq0 Integer
instance Eq0 Float
instance Eq0 Double

data Mat v a = Mat
  { _matShift                           :: {-# UNPACK #-}!Int
  , _matI, _matJ, _matHeight, _matWidth :: {-# UNPACK #-}!Word32
  , _matBody                            :: !(H.Vector U.Vector v (Key, a))
  } deriving (Show)

makeLenses ''Mat

keys :: Lens (H.Vector u v (a,b)) (H.Vector w v (c,b)) (u a) (w c)
keys f (H.V ks vs) = f ks <&> \ks' -> H.V ks' vs

values :: Lens (H.Vector u v (a,b)) (H.Vector u w (a,c)) (v b) (w c)
values f (H.V ks vs) = f vs <&> \vs' -> H.V ks vs'

instance Functor v => Functor (Mat v) where
  fmap = over (matBody.values.mapped)
  {-# INLINE fmap #-}

instance Foldable v => Foldable (Mat v) where
  foldMap = foldMapOf (matBody.values.folded)
  {-# INLINE foldMap #-}

instance Traversable v => Traversable (Mat v) where
  traverse = matBody.values.traverse
  {-# INLINE traverse #-}

type instance IxValue (Mat v a) = a
type instance Index (Mat v a) = Key

-- modify an entry in the matrix... if it exists.
instance (Applicative f, G.Vector v a) => Ixed f (Mat v a) where
  ix i f m@Mat{_matBody = H.V ks vs}
    | Just j <- ks U.!? l, i == j = indexed f i (vs G.! l) <&> \v' -> m { _matBody = H.V ks (vs G.// [(l,v')]) }
    | otherwise           = pure m
    where l = search (\j -> (ks U.! j) >= i) 0 (U.length ks)
  {-# INLINE ix #-}

instance G.Vector v a => At (Mat v a) where
  at i f m@Mat{_matBody = H.V ks vs} = case ks U.!? l of
    Just j
      | i == j -> indexed f i (Just (vs G.! l)) <&> \mv -> case mv of
        Just v  -> m { _matBody = H.V ks (vs G.// [(l,v)]) }
        Nothing  -> undefined -- delete
    _ -> indexed f i Nothing <&> \mv -> case mv of
        Just _v -> undefined -- insert v
        Nothing -> m
    where l = search (\j -> (ks U.! j) >= i) 0 (U.length ks)
  {-# INLINE at #-}

-- insert :: (PrimMonad m, G.MVector v e) => (e -> e -> Ordering) -> v (PrimState m) e -> Int -> e -> Int -> m ()

instance Eq0 (Mat v a) where
  isZero = H.null . _matBody
  {-# INLINE isZero #-}

{-
mask :: Int -> Word64
mask lzs = complement (k0 .|. shiftL k0 32)
  where k0 = bit (32-lzs) - 1
{-# INLINE mask #-}
-}

-- Build a sparse (h * w) a-valued matrix.
fromList :: G.Vector v a => Word32 -> Word32 -> [(Key, a)] -> Mat v a
fromList h w xs = mat 0 0 h w $ H.modify (Intro.sortBy (compare `on` fst)) (H.fromList xs)
{-# INLINE fromList #-}

mat :: Word32 -> Word32 -> Word32 -> Word32 -> H.Vector U.Vector v (Key, a) -> Mat v a
mat i j h w = Mat (nlz ((h-1) .|. (w-1))) i j h w
{-# INLINE mat #-}

singleton :: (G.Vector v a, Num a, Eq0 a) => Word32 -> Word32 -> Key -> a -> Mat v a
singleton h w k v
  | isZero v  = mat 0 0 h w H.empty
  | otherwise = mat 0 0 h w $ H.fromListN 1 [(k,v)]

count :: Mat v a -> Int
count = H.length . _matBody
{-# INLINE count #-}

zero :: G.Vector v a => Word32 -> Word32 -> Mat v a
zero h w = fromList h w []

-- is it worth sharing these?
ident :: (G.Vector v a, Num a) => Word32 -> Mat v a
ident w = mat 0 0 w w $ H.fromListN (fromIntegral w) [(key i i, 1) | i <- [0 .. w - 1]]

-- break into 2-fat quadrants.
--
-- Note: the keys have 'junk' on the top of the keys, but it should be exactly the junk we need them to have when we rejoin the quadrants
-- @mlzs@ gives you enough information to be able to trim them otherwise.
quadrants :: G.Vector v a => Lens' (Mat v a) (Mat v a, Mat v a, Mat v a, Mat v a)
quadrants f (Mat lzs i0 j0 h w body@(H.V ks _)) =
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

-- subject to stream fusion
mergeStreamsWith :: (Monad m, Ord i) => (a -> a -> Maybe a) -> Stream m (i, a) -> Stream m (i, a) -> Stream m (i, a)
mergeStreamsWith f (Stream stepa sa0 na) (Stream stepb sb0 nb)
  = Stream step (MergeStart sa0 sb0) (toMax na + toMax nb) where
  {-# INLINE [0] step #-}
  step (MergeStart sa sb) = do
    r <- stepa sa
    return $ case r of
      Yield (i, a) sa' -> Skip (MergeL sa' sb i a)
      Skip sa'         -> Skip (MergeStart sa' sb)
      Done             -> Skip (MergeLeftEnded sb)
  step (MergeL sa sb i a) = do
    r <- stepb sb
    return $ case r of
      Yield (j, b) sb' -> case compare i j of
        LT -> Yield (i, a)     (MergeR sa sb' j b)
        EQ -> case f a b of
           Just c  -> Yield (i, c) (MergeStart sa sb')
           Nothing -> Skip (MergeStart sa sb')
        GT -> Yield (j, b)     (MergeL sa sb' i a)
      Skip sb' -> Skip (MergeL sa sb' i a)
      Done     -> Yield (i, a) (MergeRightEnded sa)
  step (MergeR sa sb j b) = do
    r <- stepa sa
    return $ case r of
      Yield (i, a) sa' -> case compare i j of
        LT -> Yield (i, a)     (MergeR sa' sb j b)
        EQ -> case f a b of
          Just c  -> Yield (i, c) (MergeStart sa' sb)
          Nothing -> Skip (MergeStart sa' sb)
        GT -> Yield (j, b)     (MergeL sa' sb i a)
      Skip sa' -> Skip (MergeR sa' sb j b)
      Done     -> Yield (j, b) (MergeLeftEnded sb)
  step (MergeLeftEnded sb) = do
    r <- stepb sb
    return $ case r of
      Yield (j, b) sb' -> Yield (j, b) (MergeLeftEnded sb')
      Skip sb'         -> Skip (MergeLeftEnded sb')
      Done             -> Done
  step (MergeRightEnded sa) = do
    r <- stepa sa
    return $ case r of
      Yield (i, a) sa' -> Yield (i, a) (MergeRightEnded sa')
      Skip sa'         -> Skip (MergeRightEnded sa')
      Done             -> Done
{-# INLINE [1] mergeStreamsWith #-}

data MergeState sa sb i a
  = MergeL sa sb i a
  | MergeR sa sb i a
  | MergeLeftEnded sb
  | MergeRightEnded sa
  | MergeStart sa sb

data ConcatFourState sa sb sc sd
  = C4 sa sb sc sd
  | C3    sb sc sd
  | C2       sc sd
  | C1          sd

concatFour :: Monad m => Stream m a -> Stream m a -> Stream m a -> Stream m a -> Stream m a
concatFour (Stream stepa sa0 na) (Stream stepb sb0 nb) (Stream stepc sc0 nc) (Stream stepd sd0 nd)
  = Stream step (C4 sa0 sb0 sc0 sd0) (na + nb + nc + nd) where
  {-# INLINE [0] step #-}
  step (C4 sa sb sc sd) = do
    r <- stepa sa
    return $ case r of
      Yield a sa' -> Yield a (C4 sa' sb sc sd)
      Skip sa'    -> Skip (C4 sa' sb sc sd)
      Done        -> Skip (C3 sb sc sd)
  step (C3 sb sc sd) = do
    r <- stepb sb
    return $ case r of
      Yield a sb' -> Yield a (C3 sb' sc sd)
      Skip sb'    -> Skip (C3 sb' sc sd)
      Done        -> Skip (C2 sc sd)
  step (C2 sc sd) = do
    r <- stepc sc
    return $ case r of
      Yield a sc' -> Yield a (C2 sc' sd)
      Skip sc'    -> Skip (C2 sc' sd)
      Done        -> Skip (C1 sd)
  step (C1 sd) = do
    r <- stepd sd
    return $ case r of
      Yield a sd' -> Yield a (C1 sd')
      Skip sd'    -> Skip (C1 sd')
      Done        -> Done
{-# INLINE [1] concatFour #-}


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
