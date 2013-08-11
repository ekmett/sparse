{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Sparse.Matrix where

import Control.Applicative
import Control.Lens
import Data.Bits
import Data.Bits.Lens
import Data.Bits.Extras
import Data.Function (on)
import qualified Data.Vector.Algorithms.Intro as Intro
import Data.Vector.Fusion.Stream.Monadic (Step(..), Stream(..))
import Data.Vector.Fusion.Stream.Size
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Hybrid as H
import qualified Data.Vector.Hybrid.Internal as H
import qualified Data.Vector.Primitive as P
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Data.Word
-- import Debug.Trace

-- * Morton Order

-- | @key i j@ packs a 32-bit @i@ and 32-bit @j@ coordinate into the upper bits and lower bits of a 64 bit machine word respectively.
--
-- Keys are sorted in \"Morton Order\" by using bit manipulation tricks.
newtype Key = Key Word64
  deriving (Eq, P.Prim, U.Unbox, GM.MVector UM.MVector, G.Vector U.Vector)

instance Show Key where
  showsPrec d w = showParen (d > 10) $
    showString "key " . Prelude.showsPrec 11 (w^._i) .
         showChar ' ' . Prelude.showsPrec 11 (w^._j)

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
  { matShift                        :: {-# UNPACK #-}!Int
  , matI, matJ, matHeight, matWidth :: {-# UNPACK #-}!Word32
  , matBody                         :: !(H.Vector U.Vector v (Key, a))
  } deriving (Show)

-- instance G.Vector v a => Num (Mat v a) where

instance Eq0 (Mat v a) where
  isZero = H.null . matBody
  {-# INLINE isZero #-}

mask :: Int -> Word64
mask lzs = complement (k0 .|. shiftL k0 32)
  where k0 = bit (32-lzs) - 1

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
count = H.length . matBody
{-# INLINE count #-}

zero :: G.Vector v a => Word32 -> Word32 -> Mat v a
zero h w = fromList h w []

-- is it worth sharing these?
ident :: (G.Vector v a, Num a) => Word32 -> Mat v a
ident w = mat 0 0 w w $ H.fromListN (fromIntegral w) [(key i i, 1) | i <- [0 .. w - 1]]

quadrants :: G.Vector v a => Mat v a -> (Mat v a, Mat v a, Mat v a, Mat v a)
quadrants (Mat lzs i0 j0 h w body@(H.V ks _)) =
  -- traceShow ([ (rawKey k .&. hmask, rawKey k .&. lmask) | k <- U.toList ks], split1, split2, split3) $
  ( m00, m01
  , m10, m11
  ) where
    hmask = bit (63 - lzs)
    lmask = bit (31 - lzs)
    n = U.length ks
    split2 = search (\i -> (ks U.! i)^.raw .&. hmask /= 0) 0 n
    split1 = search (\i -> (ks U.! i)^.raw .&. lmask /= 0) 0 split2
    split3 = search (\i -> (ks U.! i)^.raw .&. lmask /= 0) split2 n
    (uh,lh)   = H.splitAt split1 body
    (b00,b01) = H.splitAt split1 uh
    (b10,b11) = H.splitAt (split3 - split2) lh
    m00 = Mat lzs' i0      j0      dh     dw     b00
    m01 = Mat lzs' i0      (j0+dw) dh     (w-dw) b01
    m10 = Mat lzs' (i0+dh) j0      (h-dh) dw     b10
    m11 = Mat lzs' (i0+dh) (j0+dh) (h-dw) (w-dw) b11
    dh = fattest (h - 1)
    dw = fattest (w - 1)
    lzs' = lzs + 1

-- (i x j, j x k) -> (i x k)

{-
multiply :: G.Vector v a => Mat v a -> Mat v a -> Mat v a
multiply x y
  | isZero x || isZero y = zero h w
  | count x == 1 && count y == 1, (ij,xij) <- H.head (matBody x), (jk,yjk) <- H.head (matBody y) = if ij^._j == jk^._j then singleton h w (jk&_i.~ij^._i) (xij*yjk) else zero h w
  -- at least one quadrant is non-empty, subdivide
  | otherwise =
  where (x00,x01,x10,x11) = quadrants x
        (y00,y01,y11,y11) = quadrants y
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
fattest y0 = shiftR x5 1 + 1 where
  x0 = y0 - 1
  x1 = x0 .|. shiftR x0 1
  x2 = x1 .|. shiftR x1 2
  x3 = x2 .|. shiftR x2 4
  x4 = x3 .|. shiftR x3 8
  x5 = x4 .|. shiftR x4 16

-- | assuming @l <= h@. Returns @h@ if the predicate is never @True@ over @[l..h)@
search :: (Int -> Bool) -> Int -> Int -> Int
search p = go where
  go l h
    | l == h    = l
    | p m       = go l m
    | otherwise = go (m+1) h
    where m = l + div (h-l) 2
{-# INLINE search #-}

mergeMatricesWith :: (a -> a -> Maybe a) -> Mat v a -> Mat v a -> Mat v a
mergeMatricesWith = undefined
-- mergeMatricesWith f (Mat 

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
mergeStreamsWith f (Stream stepa sa na) (Stream stepb sb nb)
  = Stream step (MergeStart sa sb) (toMax na + toMax nb) where
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

