module Poly
  ( adder
  , obs
  , leak
  , sim
  , circ
  , curIgn
  , ignCirc
  ) where

import Projection
import UC

{-# ANN adder UCTactic 
  { observation = 'obs
  , leakage = 'leak
  , simulator = 'sim
  , projections =
    [ Projection
      { ignore = 'obs
      , circuit = 'circ
      }
    ]
  } #-}
adder :: Num a => Maybe a -> Maybe (a, a) -> (Maybe a, Maybe a)
adder s i = case i of
  Just (a, b) -> (Just $ a + b, s)
  Nothing -> (Nothing, s)

-- {-# ANN curIgn UCNorm #-}
curIgn :: Num a => Eq a => Maybe a -> Maybe (a, a) -> (Maybe Bool, Maybe Bool)
curIgn = sproj obs (oproj obs adder)

-- {-# ANN ignCirc UCNorm #-}
ignCirc :: Num a => Eq a => Maybe a -> Maybe (a, a) -> (Maybe Bool, Maybe Bool)
ignCirc = sproj' obs circ

obs :: Num a => Eq a => Maybe a -> Maybe Bool
obs (Just x) = Just $ x == 0
obs _ = Nothing

leak :: Num a => Eq a => Maybe (a, a) -> Maybe Bool
leak (Just (a, b)) = Just $ a + b == 0
leak _ = Nothing

sim :: Maybe Bool -> Maybe Bool -> (Maybe Bool, Maybe Bool)
sim s i = (i, s)

circ :: Num a => Eq a => Maybe Bool -> Maybe (a, a) -> (Maybe Bool, Maybe Bool)
circ s i = case i of
  Just (a, b) -> (Just $ a + b == 0, s)
  Nothing -> (Nothing, s)
