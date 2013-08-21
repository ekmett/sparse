{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Sparse.Matrix.Heap
  ( Heap(..)
  , fby
  , mix
  , top
  , singleton
  , fromList
  , fromAscList
  , streamHeapWith
  , streamHeapWith0
  , timesSingleton
  , singletonTimes
  ) where

import Control.Applicative
import Control.Lens
import Data.Bits
import Data.Foldable
import Data.Monoid
import Data.Vector.Fusion.Stream.Monadic hiding (singleton, fromList)
import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util
import Data.Word
import Sparse.Matrix.Key

-- Bootstrapped _catenable_ non-empty pairing heaps
data Heap a = Heap {-# UNPACK #-} !Key a [Heap a] [Heap a] [Heap a]
  deriving (Show,Read)

-- append two heaps where we know every key in the first occurs before every key in the second
fby :: Heap a -> Heap a -> Heap a
fby (Heap i a as ls rs) r = Heap i a as ls (r:rs)

fbys :: Heap a -> [Heap a] -> [Heap a] -> Heap a
fbys (Heap i a as [] []) ls' rs' = Heap i a as ls' rs'
fbys (Heap i a as ls []) ls' rs' = Heap i a as ls $ rs' <> reverse ls'
fbys (Heap i a as ls rs) ls' rs' = Heap i a as ls $ rs' <> reverse ls' <> rs

-- | interleave two heaps making a new 'Heap'
mix :: Heap a -> Heap a -> Heap a
mix x0@(Heap i0 _ _ _ _) y0@(Heap j0 _ _ _ _)
  | i0 <= j0  = go x0 y0
  | otherwise = go y0 x0
  where
    go (Heap i a as [] []) x = Heap i a (x:as) [] [] -- flat
    go (Heap i a as al ar) x = case pop as al ar of  -- nest
      Nothing -> Heap i a [x] [] [] -- possible?
      Just y  -> Heap i a [x,y] [] []

top :: Heap a -> (Key, a)
top (Heap i a _ _ _) = (i, a)

-- violates the Stream fusion guidelines
pop :: [Heap a] -> [Heap a] -> [Heap a] -> Maybe (Heap a)
pop (x:xs) ls     rs = Just (fbys (meld x xs) ls rs)
  where
    meld u []     = u
    meld u (s:ss) = meld (mix u s) ss
pop []     (l:ls) rs = Just (fbys l ls rs)
pop []     []     rs = case reverse rs of
  f:fs -> Just (fbys f fs [])
  []   -> Nothing

singleton :: Key -> a -> Heap a
singleton k v = Heap k v [] [] []

fromList :: [(Key,a)] -> Heap a
fromList ((k0,v0):xs) = Prelude.foldr (\(k,v) r -> mix (singleton k v) r) (singleton k0 v0) xs
fromList [] = error "empty Heap"

fromAscList :: [(Key,a)] -> Heap a
fromAscList ((k0,v0):xs) = Prelude.foldr (\(k,v) r -> fby (singleton k v) r) (singleton k0 v0) xs
fromAscList [] = error "empty Heap"

instance Functor Heap where
  fmap f (Heap k a xs ls rs) = Heap k (f a) (fmap f <$> xs) (fmap f <$> ls) (fmap f <$> rs)

instance FunctorWithIndex Key Heap where
  imap f (Heap k a xs ls rs) = Heap k (f k a) (imap f <$> xs) (imap f <$> ls) (imap f <$> rs)

instance Foldable Heap where
  foldMap f = go where
    go (Heap _ a xs ls rs) = case pop xs ls rs of
      Nothing -> f a
      Just h  -> f a `mappend` go h
  {-# INLINE foldMap #-}

instance FoldableWithIndex Key Heap where
  ifoldMap f = go where
    go (Heap i a xs ls rs) = case pop xs ls rs of
      Nothing -> f i a
      Just h  -> f i a `mappend` go h
  {-# INLINE ifoldMap #-}

-- this linearizes the heap
instance Traversable Heap where
  traverse f xs = fromAscList <$> traverse (traverse f) (itoList xs)
  {-# INLINE traverse #-}

instance TraversableWithIndex Key Heap where
  itraverse f xs = fromAscList <$> traverse (\(k,v) -> (,) k <$> f k v) (itoList xs)
  {-# INLINE itraverse #-}

data HeapState a
  = Start !(Heap a)
  | Ready {-# UNPACK #-} !Key a !(Heap a)
  | Final {-# UNPACK #-} !Key a
  | Finished

streamHeapWith :: Monad m => (a -> a -> a) -> Maybe (Heap a) -> Stream m (Key, a)
streamHeapWith f h0 = Stream step (maybe Finished Start h0) Unknown where
  step (Start (Heap i a xs ls rs))     = return $ Skip $ maybe (Final i a) (Ready i a) $ pop xs ls rs
  step (Ready i a (Heap j b xs ls rs)) = return $ case compare i j of
    LT -> Yield (i, a)      $ maybe (Final j b) (Ready j b) $ pop xs ls rs
    EQ | c <- f a b -> Skip $ maybe (Final i c) (Ready i c) $ pop xs ls rs
    GT -> Yield (j, b)      $ maybe (Final i a) (Ready i a) $ pop xs ls rs
  step (Final i a) = return $ Yield (i,a) Finished
  step Finished    = return Done
  {-# INLINE [1] step #-}
{-# INLINE [0] streamHeapWith #-}

streamHeapWith0 :: Monad m => (a -> a -> Maybe a) -> Maybe (Heap a) -> Stream m (Key, a)
streamHeapWith0 f h0 = Stream step (maybe Finished Start h0) Unknown where
  step (Start (Heap i a xs ls rs))     = return $ Skip $ maybe (Final i a) (Ready i a) $ pop xs ls rs
  step (Ready i a (Heap j b xs ls rs)) = return $ case compare i j of
    LT -> Yield (i, a) $ maybe (Final j b) (Ready j b) $ pop xs ls rs
    EQ -> case f a b of
      Nothing -> Skip  $ maybe Finished Start $ pop xs ls rs
      Just c  -> Skip  $ maybe (Final i c) (Ready i c) $ pop xs ls rs
    GT -> Yield (j, b) $ maybe (Final i a) (Ready i a) $ pop xs ls rs
  step (Final i a) = return $ Yield (i,a) Finished
  step Finished = return Done
  {-# INLINE [1] step #-}
{-# INLINE [0] streamHeapWith0 #-}

m1, m2 :: Word64
m1 = 0xAAAAAAAAAAAAAAAA
m2 = 0x5555555555555555
{-# INLINE m1 #-}
{-# INLINE m2 #-}

-- | This is the internal stream fusion combinator used to multiply on the right by a singleton key
timesSingleton :: (a -> b -> c) -> Stream Id (Key, a) -> Key -> b -> Maybe (Heap c)
timesSingleton f (Stream stepa sa0 _) (Key jk) b = start sa0 where
  !jj = unsafeShiftR (jk .&. m1) 1
  !kk = jk .&. m2
  start sa = case unId (stepa sa) of
    Yield (Key ij, a) sa'
      | ij .&. m2 == jj -> Just $ run (singleton (Key (ij .&. m1 .|. kk)) (f a b)) sa'
      | otherwise       -> start sa'
    Skip sa' -> start sa'
    Done     -> Nothing
  run h sa = case unId (stepa sa) of
    Yield (Key ij, a) sa'
      | ij .&. m2 == jj -> run (h `mix` singleton (Key (ij .&. m1 .|. kk)) (f a b)) sa'
      | otherwise       -> run h sa'
    Skip sa' -> run h sa'
    Done     -> h
{-# INLINE timesSingleton #-}

-- | This is the internal stream fusion combinator used to multiply on the right by a singleton key
singletonTimes :: (a -> b -> c) -> Key -> a -> Stream Id (Key, b) -> Maybe (Heap c)
singletonTimes f (Key ij) a (Stream stepb sb0 _) = start sb0 where
  !jj = unsafeShiftL (ij .&. m2) 1
  !ii = ij .&. m1
  start sb = case unId (stepb sb) of
    Yield (Key jk, b) sb'
      | jk .&. m1 == jj -> Just $ run (singleton (Key (ii .|. jk .&. m2)) (f a b)) sb'
      | otherwise       -> start sb'
    Skip sb' -> start sb'
    Done     -> Nothing
  run h sb = case unId (stepb sb) of
    Yield (Key jk, b) sb'
      | jk .&. m1 == jj -> run (h `mix` singleton (Key (ii .|. jk .&. m2)) (f a b)) sb'
      | otherwise       -> run h sb'
    Skip sb' -> run h sb'
    Done     -> h
{-# INLINE singletonTimes #-}
