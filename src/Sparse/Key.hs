{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Sparse.Key
  ( Key(..)
  , key
  , shuffled
  , unshuffled
  , _i, _j
  , _ii, _jj
  ) where

import Control.Applicative
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
newtype Key = Key { rawKey :: Word64 }
  deriving (Eq, Ord, Enum, S.Storable, P.Prim, U.Unbox, GM.MVector UM.MVector, G.Vector U.Vector)

shuffled :: Iso' (Word32, Word32) Key
shuffled = iso (uncurry key) unshuffle
{-# INLINE shuffled #-}

unshuffled :: Iso' Key (Word32, Word32)
unshuffled = iso unshuffle (uncurry key)
{-# INLINE unshuffled #-}

-- | This should be order preserving
key :: Word32 -> Word32 -> Key
key i j = Key k5 where
  k0 = unsafeShiftL (fromIntegral i) 32 .|. fromIntegral j
  t0 = xor k0 (unsafeShiftR k0 16) .&. 0x00000000FFFF0000
  k1 = k0 `xor` t0 `xor` unsafeShiftL t0 16
  t1 = xor k1 (unsafeShiftR k1 8 ) .&. 0x0000FF000000FF00
  k2 = k1 `xor` t1 `xor` unsafeShiftL t1 8
  t2 = xor k2 (unsafeShiftR k2 4 ) .&. 0x00F000F000F000F0
  k3 = k2 `xor` t2 `xor` unsafeShiftL t2 4
  t3 = xor k3 (unsafeShiftR k3 2 ) .&.  0x0C0C0C0C0C0C0C0C
  k4 = k3 `xor` t3 `xor` unsafeShiftL t3 2
  t4 = xor k4 (unsafeShiftR k4 1 ) .&. 0x2222222222222222
  k5 = k4 `xor` t4 `xor` unsafeShiftL t4 1
{-# INLINE key #-}

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

mi, mj :: Word64
mi = 0xAAAAAAAAAAAAAAAA
mj = 0x5555555555555555
{-# INLINE mi #-}
{-# INLINE mj #-}

-- TODO: half shuffle
_i, _j :: Lens' Key Word32
_i = unshuffled._1
_j = unshuffled._2
{-# INLINE _i #-}
{-# INLINE _j #-}

-- | Lenses for working with masked off versions of the @i@ or @j@ column.
-- The result is spread with interleaved zeros in the odd bits.
_ii, _jj :: Lens' Key Word64
_jj f (Key ij) = f (ij .&. mj) <&> \j' -> Key $ (j' .&. mj) .|. ij .&. mi
_ii f (Key ij) = f (unsafeShiftR (ij .&. mi) 1) <&> \i' -> Key $ (unsafeShiftL i' 1 .&. mi) .|. ij .&. mj
