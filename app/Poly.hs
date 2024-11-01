module Poly
  ( adder
  , obs
  , leak
  , sim
  , proj
  , compImpl
  , compSim
  ) where

import Projection
-- import UC

-- {-# ANN adder UC
--   { observation = 'obs
--   , leakage = 'leak
--   , simulator = 'sim
--   , projection = 'proj
--   } #-}
adder :: Num a => Maybe a -> Maybe (a, a) -> (Maybe a, Maybe a)
adder s i = case i of
  Just (a, b) -> (Just $ a + b, s)
  Nothing -> (Nothing, s)

obs :: Num a => Eq a => Maybe a -> Maybe Bool
obs (Just x) = Just $ x == 0
obs _ = Nothing

leak :: Num a => Eq a => () -> Maybe (a, a) -> ((), Maybe Bool)
leak _ (Just (a, b)) = ((), Just $ a + b == 0)
leak _ _ = ((), Nothing)

sim :: Maybe Bool -> Maybe Bool -> (Maybe Bool, Maybe Bool)
sim s i = (i, s)

proj :: Num a => Eq a => Maybe a -> ((), Maybe Bool)
proj = (\s -> ((), s)) . obs

-- {-# ANN curIgn UCNorm #-}
compImpl :: Num a => Eq a => Maybe a -> Maybe (a, a) -> (((), Maybe Bool), Maybe Bool)
compImpl = sproj proj $ oproj obs adder

-- {-# ANN ignCirc UCNorm #-}
compSim :: Num a => Eq a => Maybe a -> Maybe (a, a) -> (((), Maybe Bool), Maybe Bool)
compSim = sproj' proj $ iproj leak sim

