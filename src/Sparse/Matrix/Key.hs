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
----------------------------------------------------------------------------

module Sparse.Matrix.Key
  ( Key(..)
  ) where

import Data.Bits
import Control.Monad
import Control.Lens
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Data.Word

-- * Morton Order

-- | @key i j@ interleaves the bits of the keys @i@ and @j@.
--
-- Keys are then just values sorted in \"Morton Order\".
data Key = Key {-# UNPACK #-} !Word32 {-# UNPACK #-} !Word32
  deriving (Show, Read, Eq)

instance Ord Key where
  Key a b `compare` Key c d
    | ab < cd && ab < xor ab cd = compare b d
    | otherwise = compare a c
    where ab = xor a b
          cd = xor c d

-- | Construct a key from a pair of indices.
--
-- @
-- key i j ^. _1 = i
-- key i j ^. _2 = j
-- @
key :: Word32 -> Word32 -> Key
key = Key
{-# INLINE key #-}

instance (a ~ Word32, b ~ Word32) => Field1 Key Key a b where
  _1 f (Key i j) = indexed f (0 :: Int) i <&> \i' -> Key i' j
  {-# INLINE _1 #-}

instance (a ~ Word32, b ~ Word32) => Field2 Key Key a b where
  _2 f (Key i j) = indexed f (1 :: Int) j <&> Key i
  {-# INLINE _2 #-}

instance U.Unbox Key

newtype instance U.MVector s Key = MV_Key (U.MVector s (Word32,Word32))
newtype instance U.Vector    Key = V_Key (U.Vector (Word32,Word32))

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
  basicLength (MV_Key v) = GM.basicLength v
  basicUnsafeSlice i n (MV_Key v) = MV_Key $ GM.basicUnsafeSlice i n v
  basicOverlaps (MV_Key v1) (MV_Key v2) = GM.basicOverlaps v1 v2
  basicUnsafeNew n = MV_Key `liftM` GM.basicUnsafeNew n
  basicUnsafeReplicate n (Key x y) = MV_Key `liftM` GM.basicUnsafeReplicate n (x,y)
  basicUnsafeRead (MV_Key v) i = uncurry Key `liftM` GM.basicUnsafeRead v i
  basicUnsafeWrite (MV_Key v) i (Key x y) = GM.basicUnsafeWrite v i (x,y)
  basicClear (MV_Key v) = GM.basicClear v
  basicSet (MV_Key v) (Key x y) = GM.basicSet v (x,y)
  basicUnsafeCopy (MV_Key v1) (MV_Key v2) = GM.basicUnsafeCopy v1 v2
  basicUnsafeMove (MV_Key v1) (MV_Key v2) = GM.basicUnsafeMove v1 v2
  basicUnsafeGrow (MV_Key v) n = MV_Key `liftM` GM.basicUnsafeGrow v n

instance G.Vector U.Vector Key where

  {-# INLINE basicUnsafeFreeze #-}
  {-# INLINE basicUnsafeThaw #-}
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicUnsafeIndexM #-}
  {-# INLINE elemseq #-}
  basicUnsafeFreeze (MV_Key v) = V_Key `liftM` G.basicUnsafeFreeze v
  basicUnsafeThaw (V_Key v) = MV_Key `liftM` G.basicUnsafeThaw v
  basicLength (V_Key v) = G.basicLength v
  basicUnsafeSlice i n (V_Key v) = V_Key $ G.basicUnsafeSlice i n v
  basicUnsafeIndexM (V_Key v) i = uncurry Key `liftM` G.basicUnsafeIndexM v i
  basicUnsafeCopy (MV_Key mv) (V_Key v) = G.basicUnsafeCopy mv v
  elemseq _ (Key x y) z = G.elemseq (undefined :: U.Vector Word32) x
                        $ G.elemseq (undefined :: U.Vector Word32) y z
