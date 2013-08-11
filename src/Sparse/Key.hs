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

-- | This should be order preserving
shuffle :: Key -> Word64
shuffle (Key k0) = k5 where
  k1 = shiftL (k0 .&. 0x00000000FFFF0000) 16 .|. shiftR k0 16 .&. 0x00000000FFFF0000 .|. k0 .&. 0xFFFF00000000FFFF
  k2 = shiftL (k1 .&. 0x0000FF000000FF00) 8  .|. shiftR k1 8  .&. 0x0000FF000000FF00 .|. k1 .&. 0xFF0000FFFF0000FF
  k3 = shiftL (k2 .&. 0x00F000F000F000F0) 4  .|. shiftR k2 4  .&. 0x00F000F000F000F0 .|. k2 .&. 0xF00FF00FF00FF00F
  k4 = shiftL (k3 .&. 0x0C0C0C0C0C0C0C0C) 2  .|. shiftR k3 2  .&. 0x0C0C0C0C0C0C0C0C .|. k3 .&. 0xC3C3C3C3C3C3C3C3
  k5 = shiftL (k4 .&. 0x2222222222222222) 1  .|. shiftR k4 1  .&. 0x2222222222222222 .|. k4 .&. 0x9999999999999999

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
key i j = Key $ shiftL (fromIntegral i) 32 .|. fromIntegral j
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
_i f (Key w) = (\i -> Key $ shiftL (fromIntegral i) 32 .|. (w .&. lo)) <$> f (fromIntegral (shiftR w 32))
_j f (Key w) = (\j -> Key $ (w .&. hi) .|. fromIntegral j) <$> f (fromIntegral w)
{-# INLINE _i #-}
{-# INLINE _j #-}

instance Ord Key where
  compare (Key ab) (Key cd)
    | xor a c < xor b d = compare b d
    | otherwise         = compare a c
    where
      a = shiftR ab 32
      b = ab .&. lo
      c = shiftR cd 32
      d = cd .&. lo
  {-# INLINE compare #-}
