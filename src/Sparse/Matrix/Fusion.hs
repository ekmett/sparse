{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Matrix stream fusion internals
--
-----------------------------------------------------------------------------
module Sparse.Matrix.Fusion
  ( mergeStreamsWith, mergeStreamsWith0
  , timesSingleton
  , singletonTimes
  ) where

import Data.Bits
import Data.Vector.Fusion.Stream.Monadic (Step(..), Stream(..))
import Data.Vector.Fusion.Stream.Size
import Data.Word
import Sparse.Matrix.Key

-- | The state for 'Stream' fusion that is used by 'mergeStreamsWith'.
--
-- This form permits cancellative addition.
data MergeState sa sb i a
  = MergeL sa sb i a
  | MergeR sa sb i a
  | MergeLeftEnded sb
  | MergeRightEnded sa
  | MergeStart sa sb

-- | This is the internal stream fusion combinator used to merge streams for addition.
--
-- This form permits cancellative addition.
mergeStreamsWith0 :: Monad m => (a -> a -> Maybe a) -> Stream m (Key, a) -> Stream m (Key, a) -> Stream m (Key, a)
mergeStreamsWith0 f (Stream stepa sa0 na) (Stream stepb sb0 nb)
  = Stream step (MergeStart sa0 sb0) (toMax na + toMax nb) where
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
  {-# INLINE [0] step #-}
{-# INLINE [1] mergeStreamsWith0 #-}


-- | This is the internal stream fusion combinator used to merge streams for addition.
mergeStreamsWith :: Monad m => (a -> a -> a) -> Stream m (Key, a) -> Stream m (Key, a) -> Stream m (Key, a)
mergeStreamsWith f (Stream stepa sa0 na) (Stream stepb sb0 nb)
  = Stream step (MergeStart sa0 sb0) (toMax na + toMax nb) where
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
        EQ -> Yield (i, f a b) (MergeStart sa sb')
        GT -> Yield (j, b)     (MergeL sa sb' i a)
      Skip sb' -> Skip (MergeL sa sb' i a)
      Done     -> Yield (i, a) (MergeRightEnded sa)
  step (MergeR sa sb j b) = do
    r <- stepa sa
    return $ case r of
      Yield (i, a) sa' -> case compare i j of
        LT -> Yield (i, a)     (MergeR sa' sb j b)
        EQ -> Yield (i, f a b) (MergeStart sa' sb)
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
  {-# INLINE [0] step #-}
{-# INLINE [1] mergeStreamsWith #-}

m1, m2 :: Word64
m1 = 0xAAAAAAAAAAAAAAAA
m2 = 0x5555555555555555
{-# INLINE m1 #-}
{-# INLINE m2 #-}

-- | This is the internal stream fusion combinator used to multiply on the right by a singleton key
timesSingleton :: Monad m => (a -> b -> c) -> Stream m (Key, a) -> (Key, b) -> Stream m (Key, c)
timesSingleton f (Stream stepa sa0 na) (Key jk, b) = Stream step sa0 (toMax na) where
  !jj = unsafeShiftR (jk .&. m1) 1
  !kk = jk .&. m2
  step sa = do
    r <- stepa sa
    return $ case r of
      Yield (Key ij, a) sa'
        | ij .&. m2 == jj -> Yield (Key (ij .&. m1 .|. kk), f a b) sa'
        | otherwise -> Skip sa'
      Skip sa'      -> Skip sa'
      Done -> Done
  {-# INLINE [0] step #-}
{-# INLINE [1] timesSingleton #-}

-- | This is the internal stream fusion combinator used to multiply on the left by a singleton key
singletonTimes :: Monad m => (a -> b -> c) -> (Key, a) -> Stream m (Key, b) -> Stream m (Key, c)
singletonTimes f (Key ij, a) (Stream  stepb sb0 nb) = Stream step sb0 (toMax nb) where
  !jj = unsafeShiftL (ij .&. m2) 1
  !ii = ij .&. m1
  step sb = do
    r <- stepb sb
    return $ case r of
      Yield (Key jk, b) sb'
        | jk .&. m1 == jj -> Yield (Key (ii .|. jk .&. m2), f a b) sb'
        | otherwise -> Skip sb'
      Skip sa' -> Skip sa'
      Done -> Done
  {-# INLINE [0] step #-}
{-# INLINE [1] singletonTimes #-}
