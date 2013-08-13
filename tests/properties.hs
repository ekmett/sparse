{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.Applicative
import Control.Monad (guard)
import Control.Lens
import Data.List (nub)
import Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Vector as B
import Data.Vector.Unboxed as U
import Data.Vector.Hybrid as H
import Data.Vector.Generic as G
import Data.Word
import Sparse.Matrix as SM
import Sparse.Matrix.Properties
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.QuickCheck.Function
import Linear

-- model for matrix multiplication
type Linear a = Map Word32 (Map Word32 a)

nonEmpty :: Lens' (Maybe (Map k Int)) (Map k Int)
nonEmpty f m = f (fromMaybe M.empty m) <&> \ m -> m <$ guard (not (M.null m))

toLinear :: Mat U.Vector Int -> Linear Int
toLinear = H.foldr (\(k,v) r -> r & at (k^._1) . nonEmpty . at (k^._2) ?~ v) M.empty . runMat

fromLinear :: Linear Int -> Mat U.Vector Int
fromLinear m = SM.fromList $ do
  (i, n) <- M.toList m
  (j, a) <- M.toList n
  return (key i j, a)

prop_to_from x = toLinear (fromLinear x) == M.filter (not . M.null) x
prop_from_to x = fromLinear (toLinear x) == x

prop_model :: Mat U.Vector Int -> Mat U.Vector Int -> Bool
prop_model x y = toLinear (x * y) == M.filter (not . M.null) (toLinear x !*! toLinear y)

main = $defaultMainGenerator
