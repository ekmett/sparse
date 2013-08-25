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
module Sparse.Matrix.Internal.Fusion
  ( mergeStreamsWith, mergeStreamsWith0
  ) where

import Data.Vector.Fusion.Stream.Monadic (Step(..), Stream(..))
import Data.Vector.Fusion.Stream.Size
import Sparse.Matrix.Internal.Key

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
