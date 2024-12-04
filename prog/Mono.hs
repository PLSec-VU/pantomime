module Mono
  ( adder
  , obs
  , leak
  , sim
  , compImpl
  , compSim
  -- , test
  ) where

import Projection
import UC

{-# ANN adder UC
  { observation = 'obs
  , leakage = 'leak
  , simulator = 'sim
  , projection = 'proj
  } #-}
adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
adder s i = case i of
  Just (a, b) -> (Just $ a + b, s)
  Nothing -> (Nothing, s)

-- {-# ANN compImpl UCNorm #-}
compImpl :: Maybe Int -> Maybe (Int, Int) -> (((), Maybe Bool), Maybe Bool)
compImpl = sproj proj $ oproj obs adder

-- {-# ANN compSim UCNorm #-}
compSim :: Maybe Int -> Maybe (Int, Int) -> (((), Maybe Bool), Maybe Bool)
compSim = sproj' proj $ iproj leak sim

-- {-# ANN test UCNorm #-}
-- test :: Circuit ((), Maybe Bool) (Maybe (Int, Int)) (Maybe Bool)
-- test = iproj leak

obs :: Maybe Int -> Maybe Bool
obs (Just x) = Just $ x == 0
obs _ = Nothing

leak :: () -> Maybe (Int, Int) -> ((), Maybe Bool)
leak _ (Just (a, b)) = ((), Just $ a + b == 0)
leak _ _ = ((), Nothing)

sim :: Maybe Bool -> Maybe Bool -> (Maybe Bool, Maybe Bool)
sim s i = (i, s)

proj :: Maybe Int -> ((), Maybe Bool)
proj s = ((), obs s)
