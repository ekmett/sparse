{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
-- {-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE NoMonoLocalBinds #-}

module Sparse.Matrix where

import Control.Applicative
import Control.Lens
-- import Control.Monad.Primitive
import Data.Bits
-- import Data.Bits.Extras
import Data.Foldable
import Data.Function (on)
import qualified Data.Vector.Algorithms.Intro as Intro
import qualified Data.Vector.Generic as G
-- import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Hybrid as H
import qualified Data.Vector.Hybrid.Internal as H
-- import Data.Vector.Fusion.Stream as S (Stream, fromList) -- , filter)
import qualified Data.Vector.Unboxed as U
import Data.Word
import Sparse.Key
import Sparse.Fusion
-- import Data.Typeable

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

newtype Mat v a = Mat { runMat :: H.Vector U.Vector v (Key, a) }

instance (G.Vector v a, Show a) => Show (Mat v a) where
  showsPrec d (Mat v) = showsPrec d v

instance (G.Vector v a, Read a) => Read (Mat v a) where
  readsPrec d r = [ (Mat m, t) | (m, t) <- readsPrec d r ]

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

instance (Applicative f, G.Vector v a, G.Vector v b) => Each f (Mat v a) (Mat v b) a b where
  each f (Mat v@(H.V ks _)) = Mat . H.V ks . G.fromListN (G.length v) <$> traverse f' (G.toList v) where
    f' = uncurry (indexed f)
  {-# INLINE each #-}

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
fromList :: G.Vector v a => [(Key, a)] -> Mat v a
fromList xs = Mat $ H.modify (Intro.sortBy (compare `on` fst)) $ H.fromList xs
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

-- | @smear x@ finds the smallest @2^n-1 >= x@
smear :: Word64 -> Word64
smear k0 = k5 where
  k1 = k0 .|. unsafeShiftR k0 1
  k2 = k1 .|. unsafeShiftR k1 2
  k3 = k2 .|. unsafeShiftR k2 4
  k4 = k3 .|. unsafeShiftR k3 8
  k5 = k4 .|. unsafeShiftR k4 16

-- @critical m@ assumes @count m >= 2@ and tells you the critical bit to use for @split@
critical :: G.Vector v a => Mat v a -> Word64
critical (Mat (H.V ks _)) = bits `xor` unsafeShiftR bits 1 where -- the bit we're splitting on
  lo = runKey (U.head ks)
  hi = runKey (U.last ks)
  xlh = xor lo hi
  bits = smear xlh

-- | partition (and rejoin) along the major axis into a 2-fat component and the remainder.
--
-- Note: the keys have 'junk' on the top of the keys, but it should be exactly the junk we need them to have when we rejoin the quadrants
--       or reassemble a key from matrix multiplication.
split :: G.Vector v a => Word64 -> Lens' (Mat v a) (Mat v a, Mat v a)
split mask f (Mat h@(H.V ks _)) = f (Mat m0,Mat m1) <&> \ (Mat u,Mat v) -> Mat (u H.++ v)
  where
    n = U.length ks
    k = search (\i -> runKey (ks U.! i) .&. mask /= 0) 0 n
    (m0,m1) = H.splitAt k h
{-# INLINE split #-}

instance (G.Vector v a, Num a, Eq0 a) => Num (Mat v a) where
  abs    = over each abs
  {-# INLINE abs #-}
  signum = over each signum
  {-# INLINE signum #-}
  negate = over each negate
  {-# INLINE negate #-}
  fromInteger 0 = Mat H.empty
  fromInteger _ = error "Mat: fromInteger n"
  {-# INLINE fromInteger #-}
  Mat va + Mat vb = Mat (G.unstream (mergeStreamsWith f (G.stream va) (G.stream vb))) where
    f a b = case a + b of
      c | isZero c  -> Nothing
        | otherwise -> Just c
  {-# INLINE (+) #-}
  Mat va - Mat vb = Mat (G.unstream (mergeStreamsWith f (G.stream va) (G.stream vb))) where
    f a b = case a - b of
      c | isZero c  -> Nothing
        | otherwise -> Just c
  {-# INLINE (-) #-}
  (*) = error "TODO"
  -- TODO: multiplication!

{-
multiply :: G.Vector v a => Mat v a -> Mat v a -> Mat v a
multiply x@(Mat xv) y@(Mat yv) = case compare (count x) 1 of
  LT -> zero
  EQ -> Mat (G.unstream (filterMap (\(k,v) -> undefined) (G.stream yv)))
  GT -> case x ^@? split of
  | isZero x || isZero y = zero
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

