import Control.DeepSeq
import Criterion.Main
import Data.Array.Unboxed as A
import Data.Vector.Generic as G
import Data.Vector.Unboxed as U
import Sparse.Matrix as M

instance NFData (UArray i e)

main :: IO ()
main = defaultMain
  [ bench "naive I_32"  $ nf (\x -> mmul x x) $ array ((0,0),(31,31)) $ [ ((i, j), if i == j then 1 else 0) | i <- [0..31], j <- [0..31] ]
  , bench "I_32"        $ nf (\x -> x * x) (ident 32 :: Mat U.Vector Int)
  , bench "I_64"        $ nf (\x -> x * x) (ident 64 :: Mat U.Vector Int)
  , bench "I_128"       $ nf (\x -> x * x) (ident 128 :: Mat U.Vector Int)
  -- , bench "I_256"       $ nf (\x -> x * x) (ident 256 :: Mat U.Vector Int)
  -- , bench "I_512"      $ nf (\x -> x * x) (ident 1024 :: Mat U.Vector Int)
  -- , bench "I_1024"      $ nf (\x -> x * x) (ident 1024 :: Mat U.Vector Int)
  , bench "naive 32x32" $ nf (\x -> mmul x x) $ listArray ((0,0),(31,31)) $ Prelude.replicate (32*32) 1
  , bench "32x32 Int"   $ nf (\x -> x * x) blockInt
  , bench "32x32 ()"    $ nf (\x -> multiplyWithNew const (const . Just) x x) blockUnit
  ]

blockInt :: Mat U.Vector Int
blockInt = M.fromList $ Prelude.zip [key 0 0..key 31 31] (repeat 1)

blockUnit :: Mat U.Vector ()
blockUnit = M.fromList $ Prelude.zip [key 0 0..key 31 31] (repeat ())

mmul :: UArray (Int,Int) Int -> UArray (Int,Int) Int -> UArray (Int,Int) Int
mmul x y = accumArray (+) 0 ((i0,k0),(i1,k1)) $ do
    i <- range (i0,i1)
    j <- range (max j0 j0',min j1 j1')
    k <- range (k0,k1)
    return ((i,k),x A.!(i,j) * y A.!(j,k))
  where
    ((i0,j0),(i1,j1)) = bounds x
    ((j0',k0),(j1',k1)) = bounds y
