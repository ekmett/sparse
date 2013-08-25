{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternGuards #-}
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
import Instances
import Sparse.Matrix as SM
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.QuickCheck.Function
import Linear

-- model for matrix multiplication
type Linear a = Map Word (Map Word a)

nonEmpty :: Lens' (Maybe (Map k Int)) (Map k Int)
nonEmpty f m = f (fromMaybe M.empty m) <&> \ m -> m <$ guard (not (M.null m))

-- | matrix multiplication in linear will leave empty maps inside the outer map in sparse multiplication
sane :: Linear Int -> Linear Int
sane = M.filter (not . M.null)

toLinear :: Mat U.Vector Int -> Linear Int
toLinear = sane . H.foldr (\(k,v) r -> r & at (k^._1) . nonEmpty . at (k^._2) ?~ v) M.empty . view _Mat

fromLinear :: Linear Int -> Mat U.Vector Int
fromLinear m = SM.fromList $ do
  (i, n) <- M.toList m
  (j, a) <- M.toList n
  return (Key i j, a)

prop_to_from x = toLinear (fromLinear x) == sane x
prop_from_to x = fromLinear (toLinear x) == x

prop_model :: Mat U.Vector Int -> Mat U.Vector Int -> Gen Prop
prop_model x y | z <- x * y, z' <- fromLinear (toLinear x !*! toLinear y)
  = label (show z Prelude.++ " == " Prelude.++ show z') (z == z')

main = $defaultMainGenerator
