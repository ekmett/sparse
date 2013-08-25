{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Keys in Morton order
--
-- This module provides combinators for shuffling together the bits of two
-- key components to get a key that is based on their interleaved bits.
--
-- See <http://en.wikipedia.org/wiki/Z-order_curve> for more information
-- about Morton order.
--
-- How to perform the comparison without interleaving is described in
--
-- <https://www.fpcomplete.com/user/edwardk/revisiting-matrix-multiplication-part-2>
--
----------------------------------------------------------------------------
module Sparse.Matrix.Internal.Key
  (
  -- * Keys in Morton order
    Key(..)
  , swap
  -- * Most significant bit comparisons
  , compares
  , lts, les, eqs, nes, ges, gts
  -- * Unboxed vector constructors
  , U.MVector(..)
  , U.Vector(..)
  ) where

import Data.Bits
import Control.Monad
import Control.Lens
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import Data.Word

-- * Morton Order

-- | @Key i j@ logically orders the keys as if the bits of the keys @i@ and @j@
-- were interleaved. This is equivalent to storing the keys in \"Morton Order\".
--
-- >>> Key 100 200 ^. _1
-- 100
--
-- >>> Key 100 200 ^. _2
-- 200
data Key = Key {-# UNPACK #-} !Word {-# UNPACK #-} !Word
  deriving (Show, Read, Eq)

instance Ord Key where
  Key a b `compare` Key c d
    | xor a c `lts` xor b d = compare b d
    | otherwise             = compare a c

instance (a ~ Word, b ~ Word) => Field1 Key Key a b where
  _1 f (Key i j) = indexed f (0 :: Int) i <&> (Key ?? j)
  {-# INLINE _1 #-}

instance (a ~ Word, b ~ Word) => Field2 Key Key a b where
  _2 f (Key i j) = indexed f (1 :: Int) j <&> Key i
  {-# INLINE _2 #-}

instance U.Unbox Key

data instance U.MVector s Key = MV_Key {-# UNPACK #-} !Int !(U.MVector s Word) !(U.MVector s Word)
data instance U.Vector    Key = V_Key  {-# UNPACK #-} !Int !(U.Vector Word) !(U.Vector Word)

instance GM.MVector U.MVector Key where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicOverlaps #-}
  {-# INLINE basicUnsafeNew #-}
  {-# INLINE basicUnsafeReplicate #-}
  {-# INLINE basicUnsafeRead #-}
  {-# INLINE basicUnsafeWrite #-}
  {-# INLINE basicClear #-}
  {-# INLINE basicSet #-}
  {-# INLINE basicUnsafeCopy #-}
  {-# INLINE basicUnsafeGrow #-}
  basicLength (MV_Key l _ _) = l
  basicUnsafeSlice i n (MV_Key _ u v)               = MV_Key n (GM.basicUnsafeSlice i n u) (GM.basicUnsafeSlice i n v)
  basicOverlaps (MV_Key _ u1 v1) (MV_Key _ u2 v2)   = GM.basicOverlaps u1 u2 || GM.basicOverlaps v1 v2
  basicUnsafeNew n                                  = liftM2 (MV_Key n) (GM.basicUnsafeNew n) (GM.basicUnsafeNew n)
  basicUnsafeReplicate n (Key x y)                  = liftM2 (MV_Key n) (GM.basicUnsafeReplicate n x) (GM.basicUnsafeReplicate n y)
  basicUnsafeRead (MV_Key _ u v) i                  = liftM2 Key (GM.basicUnsafeRead u i) (GM.basicUnsafeRead v i)
  basicUnsafeWrite (MV_Key _ u v) i (Key x y)       = GM.basicUnsafeWrite u i x >> GM.basicUnsafeWrite v i y
  basicClear (MV_Key _ u v)                         = GM.basicClear u >> GM.basicClear v
  basicSet (MV_Key _ u v) (Key x y)                 = GM.basicSet u x >> GM.basicSet v y
  basicUnsafeCopy (MV_Key _ u1 v1) (MV_Key _ u2 v2) = GM.basicUnsafeCopy u1 u2 >> GM.basicUnsafeCopy v1 v2
  basicUnsafeMove (MV_Key _ u1 v1) (MV_Key _ u2 v2) = GM.basicUnsafeMove u1 u2 >> GM.basicUnsafeMove v1 v2
  basicUnsafeGrow (MV_Key _ u v) n                  = liftM2 (MV_Key n) (GM.basicUnsafeGrow u n) (GM.basicUnsafeGrow v n)

instance G.Vector U.Vector Key where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeFreeze #-}
  {-# INLINE basicUnsafeThaw #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicUnsafeIndexM #-}
  {-# INLINE elemseq #-}
  basicLength (V_Key v _ _) = v
  basicUnsafeFreeze (MV_Key n u v)               = liftM2 (V_Key n) (G.basicUnsafeFreeze u) (G.basicUnsafeFreeze v)
  basicUnsafeThaw (V_Key n u v)                  = liftM2 (MV_Key n) (G.basicUnsafeThaw u) (G.basicUnsafeThaw v)
  basicUnsafeSlice i n (V_Key _ u v)             = V_Key n (G.basicUnsafeSlice i n u) (G.basicUnsafeSlice i n v)
  basicUnsafeIndexM (V_Key _ u v) i              = liftM2 Key (G.basicUnsafeIndexM u i) (G.basicUnsafeIndexM v i)
  basicUnsafeCopy (MV_Key _ mu mv) (V_Key _ u v) = G.basicUnsafeCopy mu u >> G.basicUnsafeCopy mv v
  elemseq _ (Key x y) z = G.elemseq (undefined :: U.Vector Word) x
                        $ G.elemseq (undefined :: U.Vector Word) y z

-- | Swaps the key components around
--
-- >>> swap (Key 100 200)
-- Key 200 100
swap :: Key -> Key
swap (Key i j) = Key j i
{-# INLINE swap #-}

-- | compare the position of the most significant bit of two words
--
-- >>> compares 4 7
-- EQ
--
-- >>> compares 7 9
-- LT
--
-- >>> compares 9 7
-- GT
compares :: Word -> Word -> Ordering
compares a b = case compare a b of
  LT | a < xor a b -> LT
  GT | b < xor a b -> GT
  _ -> EQ
{-# INLINE compares #-}

-- | @'lts' a b@ returns 'True' when the position of the most significant bit of @a@ is less than the position of the most signficant bit of @b@.
--
-- >>> lts 4 10
-- True
--
-- >>> lts 4 7
-- False
--
-- >>> lts 7 8
-- True
lts :: Word -> Word -> Bool
lts a b = a < b && a < xor a b
{-# INLINE lts #-}

-- | @'les' a b@ returns 'True' when the position of the most significant bit of @a@ is less than or equal to the position of the most signficant bit of @b@.
--
-- >>> les 4 10
-- True
--
-- >>> les 4 7
-- True
--
-- >>> les 7 4
-- True
--
-- >>> les 10 4
-- False
les :: Word -> Word -> Bool
les a b = a <= b || xor a b <= b
{-# INLINE les #-}

-- | @'eqs' a b@ returns 'True' when the position of the most significant bit of @a@ is equal to the position of the most signficant bit of @b@.
--
-- >>> eqs 4 7
-- True
--
-- >>> eqs 4 8
-- False
--
-- >>> eqs 7 4
-- True
--
-- >>> eqs 8 4
-- False
eqs :: Word -> Word -> Bool
eqs a b = case compare a b of
  LT -> a >= xor a b
  GT -> b >= xor a b
  EQ -> True
{-# INLINE eqs #-}

-- | @'nes' a b@ returns 'True' when the position of the most significant bit of @a@ is not equal to the position of the most signficant bit of @b@.
--
-- >>> nes 4 7
-- False
--
-- >>> nes 4 8
-- True
--
-- >>> nes 7 4
-- False
--
-- >>> nes 8 4
-- True
nes :: Word -> Word -> Bool
nes a b = case compare a b of
  LT -> a < xor a b
  GT -> b < xor a b
  EQ -> False
{-# INLINE nes #-}

-- | @'gts' a b@ returns 'True' when the position of the most significant bit of @a@ is greater than to the position of the most signficant bit of @b@.
--
-- >>> gts 4 10
-- False
--
-- >>> gts 4 7
-- False
--
-- >>> gts 7 4
-- False
--
-- >>> gts 10 4
-- True
gts :: Word -> Word -> Bool
gts a b = a > b && xor a b > b
{-# INLINE gts #-}

-- | @'gts' a b@ returns 'True' when the position of the most significant bit of @a@ is greater than or equal to the position of the most signficant bit of @b@.
--
-- >>> ges 4 10
-- False
--
-- >>> ges 4 7
-- True
--
-- >>> ges 7 4
-- True
--
-- >>> ges 10 4
-- True
ges :: Word -> Word -> Bool
ges a b = a >= b || a >= xor a b
{-# INLINE ges #-}
