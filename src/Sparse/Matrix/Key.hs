{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
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
  , key
  , shuffled, unshuffled
  ) where

import Control.Lens
import Data.Bits
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Primitive as P
import qualified Data.Vector.Storable as S
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Data.Word

-- * Morton Order

-- | @key i j@ interleaves the bits of the keys @i@ and @j@.
--
-- Keys are then just values sorted in \"Morton Order\".
newtype Key = Key { runKey :: Word64 }
  deriving (Eq, Ord, Enum, S.Storable, P.Prim, U.Unbox, GM.MVector UM.MVector, G.Vector U.Vector)

-- | Construct a key from a pair of indices.
--
-- @
-- key i j ^. _1 = i
-- key i j ^. _2 = j
-- @
key :: Word32 -> Word32 -> Key
key i j = Key k5 where
  k0 = unsafeShiftL (fromIntegral i) 32 .|. fromIntegral j
  k1 = unsafeShiftL (k0 .&. 0x00000000FFFF0000) 16 .|. unsafeShiftR k0 16 .&. 0x00000000FFFF0000 .|. k0 .&. 0xFFFF00000000FFFF
  k2 = unsafeShiftL (k1 .&. 0x0000FF000000FF00) 8  .|. unsafeShiftR k1 8  .&. 0x0000FF000000FF00 .|. k1 .&. 0xFF0000FFFF0000FF
  k3 = unsafeShiftL (k2 .&. 0x00F000F000F000F0) 4  .|. unsafeShiftR k2 4  .&. 0x00F000F000F000F0 .|. k2 .&. 0xF00FF00FF00FF00F
  k4 = unsafeShiftL (k3 .&. 0x0C0C0C0C0C0C0C0C) 2  .|. unsafeShiftR k3 2  .&. 0x0C0C0C0C0C0C0C0C .|. k3 .&. 0xC3C3C3C3C3C3C3C3
  k5 = unsafeShiftL (k4 .&. 0x2222222222222222) 1  .|. unsafeShiftR k4 1  .&. 0x2222222222222222 .|. k4 .&. 0x9999999999999999
{-# INLINE key #-}

-- | This isomorphism lets you build a key from a pair of indices.
--
-- @
-- key i j ≡ (i,j)^.shuffled
-- @
--
-- @
-- 'shuffled' . 'unshuffled' = 'id'
-- 'unshuffled' . 'shuffled' = 'id'
-- @
shuffled :: Iso' (Word32, Word32) Key
shuffled = iso (uncurry key) unshuffle
{-# INLINE shuffled #-}

-- | This isomorphism lets you build a pair of indices from a key.
unshuffled :: Iso' Key (Word32, Word32)
unshuffled = iso unshuffle (uncurry key)
{-# INLINE unshuffled #-}

unshuffle :: Key -> (Word32, Word32)
unshuffle (Key k0) = (fromIntegral (unsafeShiftR k5 32), fromIntegral k5) where
  t0 = xor k0 (unsafeShiftR k0 1 ) .&. 0x2222222222222222
  k1 = k0 `xor` t0 `xor` unsafeShiftL t0 1
  t1 = xor k1 (unsafeShiftR k1 2 ) .&. 0x0C0C0C0C0C0C0C0C
  k2 = k1 `xor` t1 `xor` unsafeShiftL t1 2
  t2 = xor k2 (unsafeShiftR k2 4 ) .&. 0x00F000F000F000F0
  k3 = k2 `xor` t2 `xor` unsafeShiftL t2 4
  t3 = xor k3 (unsafeShiftR k3 8 ) .&. 0x0000FF000000FF00
  k4 = k3 `xor` t3 `xor` unsafeShiftL t3 8
  t4 = xor k4 (unsafeShiftR k4 16) .&. 0x00000000FFFF0000
  k5 = k4 `xor` t4 `xor` unsafeShiftL t4 16
{-# INLINE unshuffle #-}

instance Field1 Key Key Word32 Word32 where
  _1 f (Key ij) = indexed f (0 :: Int) (fromIntegral k5) <&> \i -> let
         i0 = fromIntegral i
         i1 = unsafeShiftL (i0 .&. 0x00000000FFFF0000) 16 .|. i0 .&. 0xFFFF00000000FFFF
         i2 = unsafeShiftL (i1 .&. 0x0000FF000000FF00) 8  .|. i1 .&. 0xFF0000FFFF0000FF
         i3 = unsafeShiftL (i2 .&. 0x00F000F000F000F0) 4  .|. i2 .&. 0xF00FF00FF00FF00F
         i4 = unsafeShiftL (i3 .&. 0x0C0C0C0C0C0C0C0C) 2  .|. i3 .&. 0xC3C3C3C3C3C3C3C3
         i5 = unsafeShiftL (i4 .&. 0x2222222222222222) 1  .|. i4 .&. 0x9999999999999999
      in Key (unsafeShiftL i5 1 .|. ij .&. m2)
    where
      k0 = unsafeShiftR (ij .&. m1) 1
      k1 = (unsafeShiftR k0 1  .|. k0) .&. 0x3333333333333333
      k2 = (unsafeShiftR k1 2  .|. k1) .&. 0x0F0F0F0F0F0F0F0F
      k3 = (unsafeShiftR k2 4  .|. k2) .&. 0x00FF00FF00FF00FF
      k4 = (unsafeShiftR k3 8  .|. k3) .&. 0x0000FFFF0000FFFF
      k5 = (unsafeShiftR k4 16 .|. k4) .&. 0x00000000FFFFFFFF
  -- _1 = unshuffled._1 -- reference implementation
  {-# INLINE _1 #-}

instance Field2 Key Key Word32 Word32 where
  _2 f (Key ij) = indexed f (1 :: Int) (fromIntegral k5) <&> \j -> let
         j0 = fromIntegral j
         j1 = unsafeShiftL (j0 .&. 0x00000000FFFF0000) 16 .|. j0 .&. 0xFFFF00000000FFFF
         j2 = unsafeShiftL (j1 .&. 0x0000FF000000FF00) 8  .|. j1 .&. 0xFF0000FFFF0000FF
         j3 = unsafeShiftL (j2 .&. 0x00F000F000F000F0) 4  .|. j2 .&. 0xF00FF00FF00FF00F
         j4 = unsafeShiftL (j3 .&. 0x0C0C0C0C0C0C0C0C) 2  .|. j3 .&. 0xC3C3C3C3C3C3C3C3
         j5 = unsafeShiftL (j4 .&. 0x2222222222222222) 1  .|. j4 .&. 0x9999999999999999
      in Key (ij .&. m1 .|. j5)
    where
      k0 = ij .&. m2
      k1 = (unsafeShiftR k0 1  .|. k0) .&. 0x3333333333333333
      k2 = (unsafeShiftR k1 2  .|. k1) .&. 0x0F0F0F0F0F0F0F0F
      k3 = (unsafeShiftR k2 4  .|. k2) .&. 0x00FF00FF00FF00FF
      k4 = (unsafeShiftR k3 8  .|. k3) .&. 0x0000FFFF0000FFFF
      k5 = (unsafeShiftR k4 16 .|. k4) .&. 0x00000000FFFFFFFF
  -- _2 = unshuffled._2 -- reference implementation
  {-# INLINE _2 #-}

instance Show Key where
  showsPrec d w = case unshuffle w of
    (i,j) -> showParen (d > 10) $
      showString "key " . Prelude.showsPrec 11 i .
           showChar ' ' . Prelude.showsPrec 11 j

instance Read Key where
  readsPrec d = readParen (d > 10) $ \r ->
    [ (key i j, u)
    | ("key",s) <- lex r
    , (i,t) <- readsPrec 11 s
    , (j,u) <- readsPrec 11 t
    ]

-- * Utilities

-- | Masks for the interleaved components of a key
m1, m2 :: Word64
m1 = 0xAAAAAAAAAAAAAAAA
m2 = 0x5555555555555555
{-# INLINE m1 #-}
{-# INLINE m2 #-}
