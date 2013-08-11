module Sparse.Fusion
  ( mergeStreamsWith
  , concatFour
  ) where

import Data.Vector.Fusion.Stream.Monadic (Step(..), Stream(..))
import Data.Vector.Fusion.Stream.Size

mergeStreamsWith :: (Monad m, Ord i) => (a -> a -> Maybe a) -> Stream m (i, a) -> Stream m (i, a) -> Stream m (i, a)
mergeStreamsWith f (Stream stepa sa0 na) (Stream stepb sb0 nb)
  = Stream step (MergeStart sa0 sb0) (toMax na + toMax nb) where
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

-- * concatFour

data ConcatFourState sa sb sc sd
  = C4 sa sb sc sd
  | C3    sb sc sd
  | C2       sc sd
  | C1          sd

concatFour :: Monad m => Stream m a -> Stream m a -> Stream m a -> Stream m a -> Stream m a
concatFour (Stream stepa sa0 na) (Stream stepb sb0 nb) (Stream stepc sc0 nc) (Stream stepd sd0 nd)
  = Stream step (C4 sa0 sb0 sc0 sd0) (na + nb + nc + nd) where
  {-# INLINE [0] step #-}
  step (C4 sa sb sc sd) = do
    r <- stepa sa
    return $ case r of
      Yield a sa' -> Yield a (C4 sa' sb sc sd)
      Skip sa'    -> Skip (C4 sa' sb sc sd)
      Done        -> Skip (C3 sb sc sd)
  step (C3 sb sc sd) = do
    r <- stepb sb
    return $ case r of
      Yield a sb' -> Yield a (C3 sb' sc sd)
      Skip sb'    -> Skip (C3 sb' sc sd)
      Done        -> Skip (C2 sc sd)
  step (C2 sc sd) = do
    r <- stepc sc
    return $ case r of
      Yield a sc' -> Yield a (C2 sc' sd)
      Skip sc'    -> Skip (C2 sc' sd)
      Done        -> Skip (C1 sd)
  step (C1 sd) = do
    r <- stepd sd
    return $ case r of
      Yield a sd' -> Yield a (C1 sd')
      Skip sd'    -> Skip (C1 sd')
      Done        -> Done
{-# INLINE [1] concatFour #-}
