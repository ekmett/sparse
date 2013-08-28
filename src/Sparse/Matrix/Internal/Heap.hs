{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Bootstrapped /catenable/ non-empty pairing heaps as described in
--
-- <https://www.fpcomplete.com/user/edwardk/revisiting-matrix-multiplication/part-5>
-----------------------------------------------------------------------------
module Sparse.Matrix.Internal.Heap
  ( Heap(..)
  , fby
  , mix
  , singleton
  , head
  , tail
  , fromList
  , fromAscList
  , streamHeapWith
  , streamHeapWith0
  ) where

import Control.Applicative
import Control.Lens
import Data.Foldable
import Data.Monoid
import Data.Vector.Fusion.Stream.Monadic hiding (singleton, fromList, head, tail)
import Data.Vector.Fusion.Stream.Size
import Sparse.Matrix.Internal.Key
import Prelude hiding (head, tail)

-- | Bootstrapped catenable non-empty pairing heaps
data Heap a = Heap {-# UNPACK #-} !Key a [Heap a] [Heap a] [Heap a]
  deriving (Show,Read)

-- | Append two heaps where we know every key in the first occurs before every key in the second
--
-- >>> head $ singleton (Key 1 1) 1 `fby` singleton (Key 2 2) 2
-- (Key 1 1,1)
fby :: Heap a -> Heap a -> Heap a
fby (Heap i a as ls rs) r = Heap i a as ls (r:rs)

-- | Interleave two heaps making a new 'Heap'
--
-- >>> head $ singleton (Key 1 1) 1 `mix` singleton (Key 2 2) 2
-- (Key 1 1,1)
mix :: Heap a -> Heap a -> Heap a
mix x@(Heap i a as al ar) y@(Heap j b bs bl br)
  | i <= j    = Heap i a (y:pops as al ar) [] []
  | otherwise = Heap j b (x:pops bs bl br) [] []

-- |
-- >>> head $ singleton (Key 1 1) 1
-- (Key 1 1,1)
head :: Heap a -> (Key, a)
head (Heap i a _ _ _) = (i, a)

-- |
-- >>> tail $ singleton (Key 1 1) 1
-- Nothing
tail :: Heap a -> Maybe (Heap a)
tail (Heap _ _ xs fs rs) = pop xs fs rs

-- |
-- >>> singleton (Key 1 1) 1
-- Heap (Key 1 1) 1 [] [] []
singleton :: Key -> a -> Heap a
singleton k v = Heap k v [] [] []

-- | Build a 'Heap' from a jumbled up list of elements.
fromList :: [(Key,a)] -> Heap a
fromList ((k0,v0):xs) = Prelude.foldr (\(k,v) r -> mix (singleton k v) r) (singleton k0 v0) xs
fromList [] = error "empty Heap"

-- | Build a 'Heap' from an list of elements that must be in strictly ascending Morton order.
fromAscList :: [(Key,a)] -> Heap a
fromAscList ((k0,v0):xs) = Prelude.foldr (\(k,v) r -> fby (singleton k v) r) (singleton k0 v0) xs
fromAscList [] = error "empty Heap"

-- * Internals

fbys :: Heap a -> [Heap a] -> [Heap a] -> Heap a
fbys (Heap i a as [] []) ls' rs' = Heap i a as ls' rs'
fbys (Heap i a as ls []) ls' rs' = Heap i a as ls $ rs' <> reverse ls'
fbys (Heap i a as ls rs) ls' rs' = Heap i a as ls $ rs' <> reverse ls' <> rs

pops :: [Heap a] -> [Heap a] -> [Heap a] -> [Heap a]
pops xs     []     [] = xs
pops (x:xs) ls     rs = [fbys (Prelude.foldl mix x xs) ls rs]
pops []     (l:ls) rs = [fbys l ls rs]
pops []     []     rs = case reverse rs of
  f:fs -> [fbys f fs []]
  _    -> [] -- caught above by the 'go as [] []' case

pop :: [Heap a] -> [Heap a] -> [Heap a] -> Maybe (Heap a)
pop (x:xs) ls     rs = Just $ fbys (Prelude.foldl mix x xs) ls rs
pop []     (l:ls) rs = Just $ fbys l ls rs
pop []     []     rs = case reverse rs of
  f:fs -> Just (fbys f fs [])
  []   -> Nothing

-- * Instances

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

-- | Convert a 'Heap' into a 'Stream' folding together values with identical keys using the supplied
-- addition operator.
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

-- | Convert a 'Heap' into a 'Stream' folding together values with identical keys using the supplied
-- addition operator that is allowed to return a sparse 0, by returning 'Nothing'.
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
