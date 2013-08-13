{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Sparse Matrices in Morton order
--
----------------------------------------------------------------------------

module Sparse.Matrix
  (
  -- * Sparse Matrices
    Mat(..)
  -- * Keys
  , Key
  , key, shuffled, unshuffled
  -- * Construction
  , fromList
  , singleton
  , ident
  , empty
  -- * Consumption
  , count
  -- * Distinguishable Zero
  , Eq0(..)
  -- * Customization
  , addWith
  , multiplyWith, multiplyWithOld, multiplyWithNew
  , nonZero
  -- * Lenses
  , _Mat, keys, values
  ) where

import Control.Applicative hiding (empty)
import Control.Lens
import Data.Bits
import Data.Foldable
import Data.Function (on)
import qualified Data.Vector.Algorithms.Intro as Intro
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Hybrid as H
import qualified Data.Vector.Hybrid.Internal as H
import qualified Data.Vector.Unboxed as U
import Data.Word
import Prelude hiding (head, last)
import Sparse.Matrix.Fusion
import Sparse.Matrix.Key

import Debug.Trace
import Numeric.Lens
-- * Distinguishable Zero

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

-- * Sparse Matrices

newtype Mat v a = Mat { runMat :: H.Vector U.Vector v (Key, a) }
  deriving (Eq,Ord)

instance (G.Vector v a, Show a) => Show (Mat v a) where
  showsPrec d (Mat v) = showsPrec d v

instance (G.Vector v a, Read a) => Read (Mat v a) where
  readsPrec d r = [ (Mat m, t) | (m, t) <- readsPrec d r ]

-- | This isomorphism lets you access the internal structure of a matrix
_Mat :: Iso (Mat u a) (Mat v b) (H.Vector U.Vector u (Key, a)) (H.Vector U.Vector v (Key, b))
_Mat = iso runMat Mat
{-# INLINE _Mat #-}

-- | Access the keys of a matrix
keys :: Lens' (Mat v a) (U.Vector Key)
keys f = _Mat $ \ (H.V ks vs) -> f ks <&> \ks' -> H.V ks' vs
{-# INLINE keys #-}

-- | Access the keys of a matrix
values :: Lens (Mat u a) (Mat v b) (u a) (v b)
values f = _Mat $ \ (H.V ks vs) -> f vs <&> \vs' -> H.V ks vs'
{-# INLINE values #-}

instance Functor v => Functor (Mat v) where
  fmap = over (values.mapped)
  {-# INLINE fmap #-}

instance Foldable v => Foldable (Mat v) where
  foldMap = foldMapOf (values.folded)
  {-# INLINE foldMap #-}

instance Traversable v => Traversable (Mat v) where
  traverse = values.traverse
  {-# INLINE traverse #-}

type instance IxValue (Mat v a) = a
type instance Index (Mat v a) = Key

instance (Applicative f, G.Vector v a, G.Vector v b) => Each f (Mat v a) (Mat v b) a b where
  each f (Mat v@(H.V ks _)) = Mat . H.V ks . G.fromListN (G.length v) <$> traverse f' (G.toList v) where
    f' = uncurry (indexed f)
  {-# INLINE each #-}

instance (Functor f, Contravariant f, G.Vector v a) => Contains f (Mat v a) where
  contains = containsIx

instance (Applicative f, G.Vector v a) => Ixed f (Mat v a) where
  ix i f m@(Mat (H.V ks vs))
    | Just j <- ks U.!? l, i == j = indexed f i (vs G.! l) <&> \v -> Mat (H.V ks (vs G.// [(l,v)]))
    | otherwise                   = pure m
    where l = search (\j -> (ks U.! j) >= i) 0 (U.length ks)
  {-# INLINE ix #-}

instance G.Vector v a => At (Mat v a) where
  at i f (Mat kvs@(H.V ks vs)) = case ks U.!? l of
    Just j
      | i == j -> indexed f i (Just (vs G.! l)) <&> \mv -> case mv of
        Just v  -> Mat $ H.V ks (vs G.// [(l,v)])
        Nothing  -> case H.splitAt l kvs of
          (x,y) -> Mat (x H.++ H.tail y)
    _ -> indexed f i Nothing <&> \mv -> case mv of
        Just v -> case H.splitAt l kvs of -- TODO: insert v
          (x,y) -> Mat (x H.++ H.cons (i,v) y)
        Nothing -> Mat kvs
    where l = search (\j -> (ks U.! j) >= i) 0 (U.length ks)
  {-# INLINE at #-}

instance Eq0 (Mat v a) where
  isZero = H.null . runMat
  {-# INLINE isZero #-}

-- * Construction

-- | Build a sparse matrix.
fromList :: G.Vector v a => [(Key, a)] -> Mat v a
fromList xs = Mat $ H.modify (Intro.sortBy (compare `on` fst)) $ H.fromList xs
{-# INLINE fromList #-}

-- | @singleton@ makes a matrix with a singleton value at a given location
singleton :: G.Vector v a => Key -> a -> Mat v a
singleton k v = Mat $ H.singleton (k,v)
{-# INLINE singleton #-}

-- | @ident n@ makes an @n@ x @n@ identity matrix
ident :: (G.Vector v a, Num a) => Word32 -> Mat v a
ident w = Mat $ H.generate (fromIntegral w) $ \i -> let i' = fromIntegral i in (key i' i', 1)
{-# INLINE ident #-}

-- | The empty matrix
empty :: G.Vector v a => Mat v a
empty = Mat H.empty
{-# INLINE empty #-}

-- * Consumption

-- | Count the number of non-zero entries in the matrix
count :: Mat v a -> Int
count = H.length . runMat
{-# INLINE count #-}

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
  (+) = addWith $ nonZero (+)
  {-# INLINE (+) #-}
  (-) = addWith $ nonZero (-)
  {-# INLINE (-) #-}
  (*) = multiplyWith (*) $ \ a b -> case a + b of
      c | isZero c  -> Nothing
        | otherwise -> Just c
  {-# INLINE (*) #-}

-- | Remove results that are equal to zero from a simpler function.
--
-- When used with @addWith@ or @multiplyWith@'s additive argumnt
-- this can help retain the sparsity of the matrix.
nonZero :: Eq0 c => (a -> b -> c) -> a -> b -> Maybe c
nonZero f a b = case f a b of
  c | isZero c -> Nothing
    | otherwise -> Just c
{-# INLINE nonZero #-}

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

-- | @smear x@ finds the smallest @2^n-1 >= x@
smear :: Word64 -> Word64
smear k0 = k6 where
  k1 = k0 .|. unsafeShiftR k0 1
  k2 = k1 .|. unsafeShiftR k1 2
  k3 = k2 .|. unsafeShiftR k2 4
  k4 = k3 .|. unsafeShiftR k3 8
  k5 = k4 .|. unsafeShiftR k4 16
  k6 = k5 .|. unsafeShiftR k5 32
{-# INLINE smear #-}

-- | Determine the parity of
parity :: Word64 -> Bool
parity k0 = testBit k6 0 where
  k1 = k0 `xor` unsafeShiftR k0 1
  k2 = k1 `xor` unsafeShiftR k1 2
  k3 = k2 `xor` unsafeShiftR k2 4
  k4 = k3 `xor` unsafeShiftR k3 8
  k5 = k4 `xor` unsafeShiftR k4 16
  k6 = k5 `xor` unsafeShiftR k5 32
{-# INLINE parity #-}

-- | @critical m@ assumes @count m >= 2@ and tells you the mask to use for @split@
critical :: G.Vector v a => Mat v a -> Word64
critical (Mat (H.V ks _)) = smear (xor lo hi)  where -- `xor` unsafeShiftR bits 1 where -- the bit we're splitting on
  lo = runKey (U.head ks)
  hi = runKey (U.last ks)
{-# INLINE critical #-}

-- | partition along the critical bit into a 2-fat component and the remainder.
--
-- Note: the keys have 'junk' on the top of the keys, but it should be exactly the junk we need them to have when we rejoin the quadrants
--       or reassemble a key from matrix multiplication!
split :: G.Vector v a => Word64 -> Mat v a -> (Mat v a, Mat v a)
split crit (Mat h@(H.V ks _)) = (Mat m0, Mat m1)
  where
    !n = U.length ks
    !k = search (\i -> runKey (ks U.! i) .&. crit /= 0) 0 n
    (m0,m1) = H.splitAt k h
{-# INLINE split #-}

-- | Merge two matrices where the indices coincide into a new matrix. This provides for generalized
-- addition. Return 'Nothing' for zero.
--
addWith :: G.Vector v a => (a -> a -> Maybe a) -> Mat v a -> Mat v a -> Mat v a
addWith f xs ys = Mat (G.unstream (mergeStreamsWith f (G.stream (runMat xs)) (G.stream (runMat ys))))
{-# INLINE addWith #-}

-- | Multiply two matrices using the specified multiplication and addition operation.
--
-- reference implementation
multiplyWithOld :: G.Vector v a => (a -> a -> a) -> (a -> a -> Maybe a) -> Mat v a -> Mat v a -> Mat v a
{-# INLINE multiplyWithOld #-}
multiplyWithOld times plus x0 y0 = case compare (count x0) 1 of
  LT -> Mat H.empty
  EQ -> go1n x0 y0
  GT -> case compare (count y0) 1 of
      LT -> Mat H.empty
      EQ -> gon1 x0 y0
      GT -> go (critical x0) x0 (critical y0) y0
  where
    goL x cy y
      | count x == 1 = go1n x y
      | otherwise = go (critical x) x cy y
    {-# INLINE goL #-}
    goR cx x y | count y == 1 = gon1 x y
               | otherwise = go cx x (critical y) y
    {-# INLINE goR #-}
    go cx x cy y -- choose and execute a split
      | cx >= cy = case split (cx `xor` unsafeShiftR cx 1) x of
        (m0,m1) | parity cx -> goL m0 cy y `add` goL m1 cy y -- merge left and right traced out regions
                | otherwise -> goL m0 cy y `fby` goL m1 cy y -- top and bottom
      | otherwise = case split (cy `xor` unsafeShiftR cy 1) y of
        (m0,m1) | parity cy -> goR cx x m0 `fby` goR cx x m1 -- left and right
                | otherwise -> goR cx x m0 `add` goR cx x m1 -- merge top and bottom traced out regions
    gon1 (Mat x) (Mat y) = Mat $ H.modify (Intro.sortBy (compare `on` fst)) $ G.unstream (timesSingleton times (G.stream x) (H.head y))
    {-# INLINE gon1 #-}
    go1n (Mat x) (Mat y) = Mat $ H.modify (Intro.sortBy (compare `on` fst)) $ G.unstream (singletonTimes times (H.head x) (G.stream y))
    {-# INLINE go1n #-}
    add = addWith plus
    {-# INLINE add #-}
    fby (Mat l) (Mat r) = Mat (l H.++ r)
    {-# INLINE fby #-}

multiplyWith :: G.Vector v a => (a -> a -> a) -> (a -> a -> Maybe a) -> Mat v a -> Mat v a -> Mat v a
multiplyWith = multiplyWithOld
{-# INLINE multiplyWith #-}

-- | Multiply two matrices using the specified multiplication and addition operation.
multiplyWithNew :: G.Vector v a => (a -> a -> a) -> (a -> a -> Maybe a) -> Mat v a -> Mat v a -> Mat v a
{-# INLINE multiplyWithNew #-}
multiplyWithNew times plus x0 y0 = case compare (count x0) 1 of
  LT -> Mat H.empty
  EQ -> go1n (lo x0) (head x0) (lo y0) y0 (hi y0)
  GT -> case compare (count y0) 1 of
      LT -> Mat H.empty
      EQ -> gon1 (lo x0) x0 (hi x0) (lo y0) (head y0)
      GT -> go   (lo x0) x0 (hi x0) (lo y0) y0 (hi y0)
  where
    goL0 xa x ya y yb
      | count x == 1 = go1n xa (head x) ya y yb
      | otherwise    = go xa x (hi x) ya y yb
    {-# INLINE goL0 #-}

    goL1 x xb ya y yb
      | count x == 1 = go1n xb (head x) ya y yb
      | otherwise    = go (lo x) x xb ya y yb
    {-# INLINE goL1 #-}

    goR0 xa x xb ya y
      | count y == 1 = gon1 xa x xb ya (head y)
      | otherwise    = go xa x xb ya y (hi y)
    {-# INLINE goR0 #-}

    goR1 xa x xb y yb
      | count y == 1 = gon1 xa x xb yb (head y)
      | otherwise    = go xa x xb (lo y) y yb
    {-# INLINE goR1 #-}

    -- x and y have at lo 2 non-zero elements each
    go xa x xb ya y yb
      | cm <- complement evenMask
      , unsafeShiftL (cm .&. 0x5555555555555555 .&. xa) 1 /= cm .&. 0xAAAAAAAAAAAAAAAA .&. yb = traceShow (base 2 # xa, base 2 # yb) (Mat H.empty) -- we disagree on the joining column
      | mx .&. crit /= 0 = case split crit x of -- then this is the most significant difference
        (m0,m1) | oddity      -> goL0 xa m0 ya y yb `add` goL1 m1 xb ya y yb -- we split on j so we have to merge
                | otherwise   -> goL0 xa m0 ya y yb `fby` goL1 m1 xb ya y yb -- we split on i so we can concatenate
      | otherwise = case split crit y of        -- then this is the most significant
        (m0,m1) | oddity      -> goR0 xa x xb ya m0 `fby` goR1 xa x xb m1 yb -- we split on k so we can concatenate
                | otherwise   -> goR0 xa x xb ya m0 `add` goR1 xa x xb m1 yb -- we split on j so we have to merge
      where
        mx     = xor xa xb
        mask   = smear (mx .|. xor ya yb)
        oddity = parity mask
        evenMask
          | oddity = unsafeShiftL mask 1 .|. 1
          | otherwise   = mask
        crit = mask `xor` unsafeShiftR mask 1

    gon1 _ (Mat x) _ yb b = Mat $ H.modify (Intro.sortBy (compare `on` fst)) $ G.unstream (timesSingleton times (G.stream x) (Key yb, b))
    {-# INLINE gon1 #-}

    go1n xa a _ (Mat y) _ = Mat $ H.modify (Intro.sortBy (compare `on` fst)) $ G.unstream (singletonTimes times (Key xa, a) (G.stream y))
    {-# INLINE go1n #-}

    add = addWith plus
    {-# INLINE add #-}

    fby (Mat l) (Mat r) = Mat (l H.++ r)
    {-# INLINE fby #-}

    lo (Mat (H.V k _)) = runKey (U.head k)
    {-# INLINE lo #-}

    hi (Mat (H.V k _)) = runKey (U.last k)
    {-# INLINE hi #-}

    head :: G.Vector v a => Mat v a -> a
    head (Mat (H.V _ v)) = G.head v
    {-# INLINE head #-}
