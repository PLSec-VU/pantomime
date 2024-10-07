module Poly
  ( obs
  , leak
  , sim
  , circ
  , adder
  ) where

import UC

obs :: Maybe Int -> Maybe Bool
obs (Just x) = Just $ x == 0
obs _ = Nothing

leak :: Maybe (Int, Int) -> Maybe Bool
leak (Just (a, b)) = Just $ a + b == 0
leak _ = Nothing

sim :: Maybe Bool -> Maybe Bool -> (Maybe Bool, Maybe Bool)
sim s i = (i, s)

circ :: Maybe Bool -> Maybe (Int, Int) -> (Maybe Bool, Maybe Bool)
circ s i = case i of
  Just (a, b) -> (Just $ a + b == 0, s)
  Nothing -> (Nothing, s)

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
adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
adder s i = case i of
  Just (a, b) -> (Just $ a + b, s)
  Nothing -> (Nothing, s)
