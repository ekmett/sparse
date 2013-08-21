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
  ) where

import Data.Foldable
import Data.Function
import Data.Functor.Identity
import Data.Monoid
import Data.Vector.Fusion.Stream.Monadic hiding (singleton)
import Data.Vector.Fusion.Stream.Size
import Control.Applicative
import Control.Monad
import Control.Lens
import Control.Lens.Internal.Review
import Sparse.Matrix.Key

-- Bootstrapped catenable non-empty pairing heaps
data Heap a = Heap {-# UNPACK #-} !Key a [Heap a] [Heap a] [Heap a]
  deriving (Show,Read)

-- interleave two heaps where we know every key in the first occurs before every key in the second
fby :: Heap a -> Heap a -> Heap a
fby (Heap i a as ls rs) r = Heap i a as ls (r:rs)

fbys :: Heap a -> [Heap a] -> [Heap a] -> Heap a
fbys (Heap i a as [] []) ls' rs' = Heap i a as ls' rs'
fbys (Heap i a as ls []) ls' rs' = Heap i a as ls (rs' <> reverse ls')
fbys (Heap i a as ls rs) ls' rs' = Heap i a as ls (rs' <> reverse ls' <> rs)

-- | interleave two heaps making a new 'Heap'
mix :: Heap a -> Heap a -> Heap a
mix x@(Heap i a as al ar) y@(Heap j b bs bl br)
  | i <= j    = Heap i a (y:as) al ar
  | otherwise = Heap j b (x:bs) bl br

top :: Heap a -> (Key, a)
top (Heap i a _ _ _) = (i, a)

-- violates the Stream fusion guidelines
pop :: [Heap a] -> [Heap a] -> [Heap a] -> Maybe (Heap a)
pop [] [] [] = Nothing
pop (x:xs) ls rs = Just (meld x xs) where
 meld u [] = u
 meld u (s:ss) = fbys (meld (mix u s) ss) ls rs
pop [] (l:ls) rs = Just (fbys l ls rs)
pop [] [] rs = case reverse rs of
  [] -> Nothing
  f:fs -> Just (fbys f fs [])

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
      Nothing -> Skip $ maybe Finished Start $ pop xs ls rs
      Just c  -> Skip $ maybe (Final i c) (Ready i c) $ pop xs ls rs
    GT -> Yield (j, b) $ maybe (Final i a) (Ready i a) $ pop xs ls rs
  step (Final i a) = return $ Yield (i,a) Finished
  step Finished = return Done
  {-# INLINE [1] step #-}
{-# INLINE [0] streamHeapWith0 #-}
