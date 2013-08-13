-- these can't be in 'Properties.hs' or the splice fails

module Instances () where

import Control.Applicative
import Data.List (nubBy)
import Data.Map as M
import Data.Vector.Generic as G
import Sparse.Matrix as S
import Test.QuickCheck.Arbitrary

instance Arbitrary Key where
  arbitrary = key <$> arbitrary <*> arbitrary

instance (G.Vector v a, Arbitrary a) => Arbitrary (Mat v a) where
  arbitrary = S.fromList . M.toList <$> arbitrary

instance (Ord k, Arbitrary k, Arbitrary v) => Arbitrary (Map k v) where
  arbitrary = M.fromList <$> arbitrary
