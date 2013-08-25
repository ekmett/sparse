{-# OPTIONS_GHC -fno-warn-orphans #-}
import Control.Applicative
import Control.DeepSeq
import Criterion.Main
import Data.Array.Unboxed as A
import Sparse.Matrix as M
import Sparse.Matrix.Internal.Heap as Heap

instance NFData (UArray i e)

main :: IO ()
main = defaultMain
  [ bench "naive I_32"  $ nf (\x -> mmul x x) $ array ((0,0),(31,31)) $ [ ((i, j), if i == j then 1 else 0) | i <- [0..31], j <- [0..31] ]
  , bench "I_32 new"     $ nf (\x -> x * x) (ident 32 :: Mat Int)
  , bench "I_64 new"     $ nf (\x -> x * x) (ident 64 :: Mat Int)
  , bench "I_128 new"    $ nf (\x -> x * x) (ident 128 :: Mat Int)
  -- , bench "I_256"       $ nf (\x -> x * x) (ident 256 :: Mat Int)
  -- , bench "I_512"      $ nf (\x -> x * x) (ident 1024 :: Mat Int)
  -- , bench "I_1024"      $ nf (\x -> x * x) (ident 1024 :: Mat Int)
  , bench "naive 32x32"  $ nf (\x -> mmul x x) $ listArray ((0,0),(31,31)) $ Prelude.replicate (32*32) 1
  , bench "32x32 Int"    $ nf (\x -> x * x) blockInt
  , bench "32x32 ()"     $ nf (\x -> multiplyWith const (Heap.streamHeapWith const) x x) blockUnit
  , bench "naive 128x128"  $ nf (\x -> mmul x x) $ listArray ((0,0),(127,127)) $ Prelude.replicate (128*128) 1
  , bench "128x128 Int"    $ nf (\x -> x * x) blockInt128
  , bench "128x128 ()"     $ nf (\x -> multiplyWith const (Heap.streamHeapWith const) x x) blockUnit128
  ]

blockInt :: Mat Int
blockInt = M.fromList $ Prelude.zip (Key <$> [0..31] <*> [0..31]) (repeat 1)

blockInt128 :: Mat Int
blockInt128 = M.fromList $ Prelude.zip (Key <$> [0..127] <*> [0..127]) (repeat 1)

blockUnit :: Mat ()
blockUnit = M.fromList $ Prelude.zip (Key <$> [0..31] <*> [0..31]) (repeat ())

blockUnit128 :: Mat ()
blockUnit128 = M.fromList $ Prelude.zip (Key <$> [0..127] <*> [0..127]) (repeat ())

mmul :: UArray (Int,Int) Int -> UArray (Int,Int) Int -> UArray (Int,Int) Int
mmul x y = accumArray (+) 0 ((i0,k0),(i1,k1)) $ do
    i <- range (i0,i1)
    j <- range (max j0 j0',min j1 j1')
    k <- range (k0,k1)
    return ((i,k),x A.!(i,j) * y A.!(j,k))
  where
    ((i0,j0),(i1,j1)) = bounds x
    ((j0',k0),(j1',k1)) = bounds y
