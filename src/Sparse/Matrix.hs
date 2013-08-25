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
{-# LANGUAGE StandaloneDeriving #-}

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
  , Key(..)
  -- * Construction
  , Sparse.Matrix.fromList
  , Sparse.Matrix.singleton
  , transpose
  , ident
  , empty
  -- * Consumption
  , size
  , null
  -- * Distinguishable Zero
  , Eq0(..)
  -- * Customization
  , addWith
  , multiplyWith
  -- * Storage
  , Vectored(..)
  -- * Lenses
  , _Mat, keys, values
  ) where

import Control.Applicative hiding (empty)
import Control.Arrow
import Control.DeepSeq
import Control.Lens
import Data.Bits
import Data.Complex
import Data.Function (on)
import qualified Data.Vector as V
import qualified Data.Vector.Algorithms.Insertion as Sort
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Hybrid as H
import qualified Data.Vector.Hybrid.Internal as H
import qualified Data.Vector.Unboxed as U
import Data.Vector.Fusion.Stream (Stream, sized)
import Data.Vector.Fusion.Stream.Size
import Data.Word
import Prelude hiding (head, last, null)
import Sparse.Matrix.Internal.Fusion as Fusion
import Sparse.Matrix.Internal.Key
import Sparse.Matrix.Internal.Vectored as I
import Sparse.Matrix.Internal.Heap as Heap hiding (head)
import Text.Read

-- import Debug.Trace
-- import Numeric.Lens

-- * Distinguishable Zero

class (Vectored a, Num a) => Eq0 a where
  -- | Return whether or not the element is 0.
  --
  -- It may be okay to never return 'True', but you won't be
  -- able to thin spurious zeroes introduced into your matrix.
  --
  isZero :: a -> Bool
#ifndef HLINT
  default isZero :: (Num a, Eq a) => a -> Bool
  isZero = (0 ==)
  {-# INLINE isZero #-}
#endif

  -- | Remove results that are equal to zero from a simpler function.
  --
  -- When used with @addWith@ or @multiplyWith@'s additive argument
  -- this can help retain the sparsity of the matrix.
  nonZero :: (x -> y -> a) -> x -> y -> Maybe a
  nonZero f a b = case f a b of
    c | isZero c -> Nothing
      | otherwise -> Just c
  {-# INLINE nonZero #-}

  -- |
  -- Add two matrices. By default this assumes 'isZero' can
  -- possibly return 'True' after an addition. For some
  -- ring-like structures, this doesn't hold. There you can
  -- use:
  --
  -- @
  -- 'addMats' = 'addWith' ('+')
  -- @
  --
  -- By default this will use
  --
  -- @
  -- 'addMats' = 'addWith0' '$' 'nonZero' ('+')
  -- @
  addMats :: Mat a -> Mat a -> Mat a
  addMats = addWith0 $ nonZero (+)
  {-# INLINE addMats #-}

  -- | Convert from a 'Heap' to a 'Stream'.
  --
  -- If addition of non-zero valus in your ring-like structure
  -- cannot yield zero, then you can use
  --
  -- @
  -- 'addHeap' = 'Heap.streamHeapWith' ('+')
  -- @
  --
  -- instead of the default definition:
  --
  -- @
  -- 'addHeap' = 'Heap.streamHeapWith0' '$' 'nonZero' ('+')
  -- @
  addHeap :: Maybe (Heap a) -> Stream (Key, a)
  addHeap = Heap.streamHeapWith0 $ nonZero (+)

instance Eq0 Int
instance Eq0 Word
instance Eq0 Integer
instance Eq0 Float
instance Eq0 Double
instance (RealFloat a, Eq0 a) => Eq0 (Complex a) where
  isZero (a :+ b) = isZero a && isZero b
  {-# INLINE isZero #-}

-- * Sparse Matrices

-- invariant: all vectors are the same length
data Mat a = Mat {-# UNPACK #-} !Int !(U.Vector Word) !(U.Vector Word) !(I.Vector a)
 --  deriving (Eq,Ord)

deriving instance (Vectored a, Eq (I.Vector a)) => Eq (Mat a)
-- Mat n xs ys vs == Mat n' xs' ys' vs' = n == n' && xs == xs' && ys == ys' && vs == vs'

deriving instance (Vectored a, Ord (I.Vector a)) => Ord (Mat a)

instance (Vectored a, Show a) => Show (Mat a) where
  showsPrec d m = G.showsPrec d (m^._Mat)

instance (Vectored a, Read a) => Read (Mat a) where
  readPrec = (_Mat # ) <$> G.readPrec

instance NFData (I.Vector a) => NFData (Mat a) where
  rnf (Mat _ xs ys vs) = rnf xs `seq` rnf ys `seq` rnf vs `seq` ()

-- | bundle up the matrix in a form suitable for vector-algorithms
_Mat :: Vectored a => Iso' (Mat a) (H.Vector U.Vector (Vec a) (Key, a))
_Mat = iso (\(Mat n xs ys vs) -> H.V (V_Key n xs ys) vs)
           (\(H.V (V_Key n xs ys) vs) -> Mat n xs ys vs)
{-# INLINE _Mat #-}

-- | Access the keys of a matrix
keys :: Lens' (Mat a) (U.Vector Key)
keys f (Mat n xs ys vs) = f (V_Key n xs ys) <&> \ (V_Key n' xs' ys') -> Mat n' xs' ys' vs
{-# INLINE keys #-}

-- | Access the keys of a matrix
values :: Lens (Mat a) (Mat b) (I.Vector a) (I.Vector b)
values f (Mat n xs ys vs) = Mat n xs ys <$> f vs
{-# INLINE values #-}

type instance IxValue (Mat a) = a
type instance Index (Mat a) = Key

-- traverse a Vector
eachV :: (Applicative f, G.Vector v a, G.Vector v b) => (a -> f b) -> v a -> f (v b)
eachV f v = G.fromListN (G.length v) <$> traverse f (G.toList v)

instance (Applicative f, Vectored a, a ~ b) => Each f (Mat a) (Mat b) a b where
  each f = _Mat $ eachV $ \(k,v) -> (,) k <$> indexed f k v
  {-# INLINE each #-}

instance (Functor f, Contravariant f, Vectored a) => Contains f (Mat a) where
  contains = containsIx

instance (Applicative f, Vectored a) => Ixed f (Mat a) where
  ix ij@(Key i j) f m@(Mat n xs ys vs)
    | Just i' <- xs U.!? l, i == i'
    , Just j' <- ys U.!? l, j == j' = indexed f ij (vs G.! l) <&> \v -> Mat n xs ys (vs G.// [(l,v)])
    | otherwise = pure m
    where l = search (\k -> Key (xs U.! k) (ys U.! k) >= ij) 0 n
  {-# INLINE ix #-}

instance Vectored a => Vectored (Mat a) where
  type Vec (Mat a) = V.Vector -- boxed

instance (Vectored a, Eq0 a) => Eq0 (Mat a) where
  isZero (Mat n _ _ _) = n == 0
  {-# INLINE isZero #-}

-- * Construction

-- | Build a sparse matrix.
fromList :: Vectored a => [(Key, a)] -> Mat a
fromList xs = _Mat # H.modify (Sort.sortBy (compare `on` fst)) (H.fromList xs)
{-# INLINABLE fromList #-}

-- | Transpose a matrix
transpose :: Vectored a => Mat a -> Mat a
transpose xs = xs & _Mat %~ H.modify (Sort.sortBy (compare `on` fst)) . H.map (first swap)
{-# INLINE transpose #-}

-- | @singleton@ makes a matrix with a singleton value at a given location
singleton :: Vectored a => Key -> a -> Mat a
singleton k v = _Mat # H.singleton (k,v)
{-# INLINE singleton #-}

-- | @ident n@ makes an @n@ x @n@ identity matrix
--
-- >>> ident 4
-- fromList [(Key 0 0,1),(Key 1 1,1),(Key 2 2,1),(Key 3 3,1)]
ident :: (Vectored a, Num a) => Int -> Mat a
ident w = Mat w (U.generate w fromIntegral) (U.generate w fromIntegral) (G.replicate w 1)
{-# INLINE ident #-}

-- | The empty matrix
--
-- >>> empty :: Mat Int
-- fromList []
empty :: Vectored a => Mat a
empty = Mat 0 U.empty U.empty G.empty
{-# INLINE empty #-}

-- * Consumption

-- | Count the number of non-zero entries in the matrix
--
-- >>> size (ident 4)
-- 4
size :: Mat a -> Int
size (Mat n _ _ _) = n
{-# INLINE size #-}

-- |
-- >>> null (empty :: Mat Int)
-- True
null :: Mat a -> Bool
null (Mat n _ _ _) = n == 0
{-# INLINE null #-}

instance (Vectored a, Eq0 a) => Num (Mat a) where
  {-# SPECIALIZE instance Num (Mat Int) #-}
  {-# SPECIALIZE instance Num (Mat Double) #-}
  {-# SPECIALIZE instance Num (Mat (Complex Double)) #-}
  abs    = over each abs
  {-# INLINE abs #-}
  signum = over each signum
  {-# INLINE signum #-}
  negate = over each negate
  {-# INLINE negate #-}
  fromInteger 0 = empty
  fromInteger _ = error "Mat: fromInteger n"
  {-# INLINE fromInteger #-}
  (+) = addMats
  {-# INLINE (+) #-}
  (-) = addWith0 $ nonZero (-)
  {-# INLINE (-) #-}
  (*) = multiplyWith (*) addHeap
  {-# INLINE (*) #-}

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

split1 :: Vectored a => Word -> Word -> Mat a -> (Mat a, Mat a)
split1 ai bi (Mat n xs ys vs) = (m0,m1)
  where
    !aibi = xor ai bi
    !k    = search (\l -> xor (xs U.! l) bi `lts` aibi) 0 n
    (xs0,xs1) = U.splitAt k xs
    (ys0,ys1) = U.splitAt k ys
    (vs0,vs1) = G.splitAt k vs
    !m0 = Mat k     xs0 ys0 vs0
    !m1 = Mat (n-k) xs1 ys1 vs1
{-# INLINE split1 #-}

split2 :: Vectored a => Word -> Word -> Mat a -> (Mat a, Mat a)
split2 aj bj (Mat n xs ys vs) = (m0,m1)
  where
    !ajbj = xor aj bj
    !k    = search (\l -> xor (ys U.! l) bj `lts` ajbj) 0 n
    (xs0,xs1) = U.splitAt k xs
    (ys0,ys1) = U.splitAt k ys
    (vs0,vs1) = G.splitAt k vs
    !m0 = Mat k     xs0 ys0 vs0
    !m1 = Mat (n-k) xs1 ys1 vs1
{-# INLINE split2 #-}

-- | Merge two matrices where the indices coincide into a new matrix. This provides for generalized
-- addition, but where the summation of two non-zero entries is necessarily non-zero.
addWith :: Vectored a => (a -> a -> a) -> Mat a -> Mat a -> Mat a
addWith f xs ys = _Mat # G.unstream (mergeStreamsWith f (G.stream (xs^._Mat)) (G.stream (ys^._Mat)))
{-# INLINE addWith #-}

-- | Merge two matrices where the indices coincide into a new matrix. This provides for generalized
-- addition. Return 'Nothing' for zero.
addWith0 :: Vectored a => (a -> a -> Maybe a) -> Mat a -> Mat a -> Mat a
addWith0 f xs ys = _Mat # G.unstream (mergeStreamsWith0 f (G.stream (xs^._Mat)) (G.stream (ys^._Mat)))
{-# INLINE addWith0 #-}

-- | Multiply two matrices using the specified multiplication and addition operation.
multiplyWith :: Vectored a => (a -> a -> a) -> (Maybe (Heap a) -> Stream (Key, a)) -> Mat a -> Mat a -> Mat a
{-# INLINEABLE multiplyWith #-}
multiplyWith times make x0 y0 = case compare (size x0) 1 of
  LT -> empty
  EQ | size y0 == 1 -> _Mat # (G.unstream $ hint $ make $ go11 (lo x0) (head x0) (lo y0) (head y0))
     | otherwise    -> _Mat # (G.unstream $ hint $ make $ go12 (lo x0) (head x0) (lo y0) y0 (hi y0))
  GT -> case compare (size y0) 1 of
      LT -> empty
      EQ -> _Mat # (G.unstream $ hint $ make $ go21 (lo x0) x0 (hi x0) (lo y0) (head y0))
      GT -> _Mat # (G.unstream $ hint $ make $ go22 (lo x0) x0 (hi x0) (lo y0) y0 (hi y0))
  where
    hint x = sized x $ Max (size x0 * size y0)
    go11 (Key i j) a (Key j' k) b
       | j == j' = Just $ Heap.singleton (Key i k) (times a b)
       | otherwise = Nothing

    -- internal cases in go22
    go22L0 xa x ya y yb
      | size x == 1 = go12 xa (head x) ya y yb
      | otherwise    = go22 xa x (hi x) ya y yb
    {-# INLINE go22L0 #-}

    go22L1 x xb ya y yb
      | size x == 1 = go12 xb (head x) ya y yb
      | otherwise    = go22 (lo x) x xb ya y yb
    {-# INLINE go22L1 #-}

    go22R0 xa x xb ya y
      | size y == 1 = go21 xa x xb ya (head y)
      | otherwise    = go22 xa x xb ya y (hi y)
    {-# INLINE go22R0 #-}

    go22R1 xa x xb y yb
      | size y == 1 = go21 xa x xb yb (head y)
      | otherwise    = go22 xa x xb (lo y) y yb
    {-# INLINE go22R1 #-}

    -- x and y have at least 2 non-zero elements each
    go22 xa@(Key xai xaj) x xb@(Key xbi xbj) ya@(Key yaj yak) y yb@(Key ybj ybk)
      | gts (xor xaj yaj) (xiyj .|. ykxj) = Nothing
      | ges xiyj ykxj
      = if ges xi yj then case split1 xai xbi x of (m0,m1) -> go22L0 xa m0 ya y yb `mfby` go22L1 m1 xb ya y yb -- we can split on i, fby
                     else case split1 yaj ybj y of (m0,m1) -> go22R0 xa x xb ya m0 `madd` go22R1 xa x xb m1 yb -- we split on j, mix
      | ges yk xj       = case split2 yak ybk y of (m0,m1) -> go22R0 xa x xb ya m0 `mfby` go22R1 xa x xb m1 yb -- we can split on k, fby
      | otherwise       = case split2 xaj xbj x of (m0,m1) -> go22L0 xa m0 ya y yb `madd` go22L1 m1 xb ya y yb -- we split on j, mix
      where
        xi = xor xai xbi
        xj = xor xaj xbj
        yj = xor yaj ybj
        yk = xor yak ybk
        xiyj = xi .|. yj
        ykxj = yk .|. xj

    go21 _ mx _ yb b = Heap.timesSingleton times (G.stream (mx^._Mat)) yb b -- linear scan. use tree and fast rejects?
    go12 xa a _ my _ = Heap.singletonTimes times xa a (G.stream (my^._Mat))

    madd Nothing xs = xs
    madd xs Nothing = xs
    madd (Just x) (Just y) = Just (mix x y)
    {-# INLINE madd #-}

    mfby Nothing xs = xs
    mfby xs Nothing = xs
    mfby (Just x) (Just y) = Just (fby x y)
    {-# INLINE mfby #-}

    lo (Mat _ xs ys _) = Key (U.head xs) (U.head ys)
    {-# INLINE lo #-}

    hi (Mat _ xs ys _) = Key (U.last xs) (U.last ys)
    {-# INLINE hi #-}

    head (Mat _ _ _ vs) = G.head vs
    {-# INLINE head #-}
