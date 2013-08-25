{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Sparse.Matrix.Internal.Vectored
  ( Vectored(..)
  , Vector
  -- * Internals
  , V_Complex(V_Complex)
  , MV_Complex(MV_Complex)
  ) where

import Control.Monad
import Data.Complex
import Data.Int
import Data.Monoid
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Fusion.Stream as Stream
import qualified Data.Vector as B
import Data.Word
import qualified Sparse.Matrix.Internal.Key as Key
import Text.Read

-- * Data types that know how to store themselves in a Vector optimally, maximizing the level of unboxing provided.

type Vector a = Vec a a

class (G.Vector (Vec a) a, Monoid (Vec a a)) => Vectored a where
  type Vec a :: * -> *
  type Vec a = U.Vector

-- * Unboxed vectors

instance Vectored ()
instance Vectored Double
instance Vectored Float
instance Vectored Int
instance Vectored Int8
instance Vectored Int16
instance Vectored Int32
instance Vectored Int64
instance Vectored Key.Key
instance Vectored Word
instance Vectored Word8
instance Vectored Word16
instance Vectored Word32
instance Vectored Word64

-- * Boxed vectors

instance Vectored Integer where
  type Vec Integer = B.Vector

-- * Complex numbers are boxed or unboxed based on their components

#ifndef HLINT
data MV_Complex :: * -> * -> * where
  MV_Complex :: {-# UNPACK #-} !Int -> !(G.Mutable (Vec a) s a) -> !(G.Mutable (Vec a) s a) -> MV_Complex s (Complex a)

data V_Complex :: * -> * where
  V_Complex :: {-# UNPACK #-} !Int -> !(Vector a) -> !(Vector a) -> V_Complex (Complex a)
#endif

type instance G.Mutable V_Complex = MV_Complex

instance (Vectored a, RealFloat a) => GM.MVector MV_Complex (Complex a) where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicOverlaps #-}
  {-# INLINE basicUnsafeNew #-}
  {-# INLINE basicUnsafeReplicate #-}
  {-# INLINE basicUnsafeRead #-}
  {-# INLINE basicUnsafeWrite #-}
  {-# INLINE basicClear #-}
  {-# INLINE basicSet #-}
  {-# INLINE basicUnsafeCopy #-}
  {-# INLINE basicUnsafeGrow #-}
  basicLength (MV_Complex l _ _) = l
  basicUnsafeSlice i n (MV_Complex _ u v)                   = MV_Complex n (GM.basicUnsafeSlice i n u) (GM.basicUnsafeSlice i n v)
  basicOverlaps (MV_Complex _ u1 v1) (MV_Complex _ u2 v2)   = GM.basicOverlaps u1 u2 || GM.basicOverlaps v1 v2
  basicUnsafeNew n                                          = liftM2 (MV_Complex n) (GM.basicUnsafeNew n) (GM.basicUnsafeNew n)
  basicUnsafeReplicate n (x :+ y)                           = liftM2 (MV_Complex n) (GM.basicUnsafeReplicate n x) (GM.basicUnsafeReplicate n y)
  basicUnsafeRead (MV_Complex _ u v) i                      = liftM2 (:+) (GM.basicUnsafeRead u i) (GM.basicUnsafeRead v i)
  basicUnsafeWrite (MV_Complex _ u v) i (x :+ y)            = GM.basicUnsafeWrite u i x >> GM.basicUnsafeWrite v i y
  basicClear (MV_Complex _ u v)                             = GM.basicClear u >> GM.basicClear v
  basicSet (MV_Complex _ u v) (x :+ y)                      = GM.basicSet u x >> GM.basicSet v y
  basicUnsafeCopy (MV_Complex _ u1 v1) (MV_Complex _ u2 v2) = GM.basicUnsafeCopy u1 u2 >> GM.basicUnsafeCopy v1 v2
  basicUnsafeMove (MV_Complex _ u1 v1) (MV_Complex _ u2 v2) = GM.basicUnsafeMove u1 u2 >> GM.basicUnsafeMove v1 v2
  basicUnsafeGrow (MV_Complex _ u v) n                      = liftM2 (MV_Complex n) (GM.basicUnsafeGrow u n) (GM.basicUnsafeGrow v n)

instance (Vectored a, RealFloat a) => G.Vector V_Complex (Complex a) where
  {-# INLINE basicLength #-}
  {-# INLINE basicUnsafeFreeze #-}
  {-# INLINE basicUnsafeThaw #-}
  {-# INLINE basicUnsafeSlice #-}
  {-# INLINE basicUnsafeIndexM #-}
  {-# INLINE elemseq #-}
  basicLength (V_Complex v _ _) = v
  basicUnsafeFreeze (MV_Complex n u v)                   = liftM2 (V_Complex n) (G.basicUnsafeFreeze u) (G.basicUnsafeFreeze v)
  basicUnsafeThaw (V_Complex n u v)                      = liftM2 (MV_Complex n) (G.basicUnsafeThaw u) (G.basicUnsafeThaw v)
  basicUnsafeSlice i n (V_Complex _ u v)                 = V_Complex n (G.basicUnsafeSlice i n u) (G.basicUnsafeSlice i n v)
  basicUnsafeIndexM (V_Complex _ u v) i                  = liftM2 (:+) (G.basicUnsafeIndexM u i) (G.basicUnsafeIndexM v i)
  basicUnsafeCopy (MV_Complex _ mu mv) (V_Complex _ u v) = G.basicUnsafeCopy mu u >> G.basicUnsafeCopy mv v
  elemseq _ (x :+ y) z = G.elemseq (undefined :: Vec a a) x
                       $ G.elemseq (undefined :: Vec a a) y z

instance (Vectored a, RealFloat a, Show a, b ~ Complex a) => Show (V_Complex b) where
  showsPrec = G.showsPrec

instance (Vectored a, RealFloat a, Read a, b ~ Complex a) => Read (V_Complex b) where
  readPrec = G.readPrec
  readListPrec = readListPrecDefault

instance (Vectored a, RealFloat a, Eq a, b ~ Complex a) => Eq (V_Complex b) where
  xs == ys = Stream.eq (G.stream xs) (G.stream ys)
  {-# INLINE (==) #-}

instance (Vectored a, RealFloat a, b ~ Complex a) => Monoid (V_Complex b) where
  mappend = (G.++)
  {-# INLINE mappend #-}
  mempty = G.empty
  {-# INLINE mempty #-}
  mconcat = G.concat
  {-# INLINE mconcat #-}

instance (Vectored a, RealFloat a) => Vectored (Complex a) where
  type Vec (Complex a) = V_Complex
