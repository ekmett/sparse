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
  , key, raw
  , _i, _j
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

-- | @key i j@ packs a 32-bit @i@ and 32-bit @j@ coordinate into the upper bits and lower bits of a 64 bit machine word respectively.
--
-- Keys are sorted in \"Morton Order\" by using bit manipulation tricks.
newtype Key = Key Word64
  deriving (Eq, S.Storable, P.Prim, U.Unbox, GM.MVector UM.MVector, G.Vector U.Vector)

shuffled :: Iso' Key Word64
shuffled = iso shuffle unshuffle

-- | This should be order preserving
shuffle :: Key -> Word64
shuffle (Key k0) = k5 where
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

unshuffle :: Word64 -> Key
unshuffle k0 = Key k5 where
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

-- these are expensive to iterate
instance Enum Key where
  succ k = k & shuffled +~ 1
  pred k = k & shuffled -~ 1
  fromEnum k = fromIntegral (k^.shuffled)
  toEnum i = fromIntegral i^.from shuffled
  enumFrom i = enumFrom (i^.shuffled)^..folded.from shuffled
  enumFromTo i j = enumFromTo (i^.shuffled) (j^.shuffled)^..folded.from shuffled
  enumFromThen i j = enumFromThen (i^.shuffled) (j^.shuffled)^..folded.from shuffled
  enumFromThenTo i j k = enumFromThenTo (i^.shuffled) (j^.shuffled) (k^.shuffled)^..folded.from shuffled

-- xor (b .&. (b - 1)) b -- should be the least significant set bit, can we abuse these to figure out succ?

instance Show Key where
  showsPrec d w = showParen (d > 10) $
    showString "key " . Prelude.showsPrec 11 (w^._i) .
         showChar ' ' . Prelude.showsPrec 11 (w^._j)

instance Read Key where
  readsPrec d = readParen (d > 10) $ \r ->
    [ (key i j, u)
    | ("key",s) <- lex r
    , (i,t) <- readsPrec 11 s
    , (j,u) <- readsPrec 11 t
    ]

key :: Word32 -> Word32 -> Key
key i j = Key $ unsafeShiftL (fromIntegral i) 32 .|. fromIntegral j
{-# INLINE key #-}

raw :: Iso' Key Word64
raw = iso (\(Key a) -> a) Key
{-# INLINE raw #-}

lo, hi :: Word64
lo = 0x00000000ffffffff
hi = 0xffffffff00000000
{-# INLINE lo #-}
{-# INLINE hi #-}

_i, _j :: Lens' Key Word32
_i f (Key w) = (\i -> Key $ unsafeShiftL (fromIntegral i) 32 .|. (w .&. lo)) <$> f (fromIntegral (unsafeShiftR w 32))
_j f (Key w) = (\j -> Key $ (w .&. hi) .|. fromIntegral j) <$> f (fromIntegral w)
{-# INLINE _i #-}
{-# INLINE _j #-}

instance Ord Key where
  compare (Key ab) (Key cd)
    | xac < xbd && xac < xor xac xbd = compare b d
    | otherwise = compare a c
    where
      a = unsafeShiftR ab 32
      b = ab .&. lo
      c = unsafeShiftR cd 32
      d = cd .&. lo
      xac = xor a c
      xbd = xor b d
  {-# INLINE compare #-}
