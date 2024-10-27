module Poly2
  ( sim
  , circ
  , adder
  , obs
  , leak
  ) where

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

obs :: Num a => Ord a => Maybe a -> Maybe Ordering
obs (Just x) = Just $ compare x 0
obs _ = Nothing

leak :: Ord a => Num a => Maybe (a, a) -> Maybe Ordering
leak (Just (x, y)) = Just $ compare (x + y) 0
leak _ = Nothing

sim :: Maybe Ordering -> Maybe Ordering -> (Maybe Ordering, Maybe Ordering)
sim s i = (i, s)

circ :: Num b => Ord b => Maybe Ordering -> Maybe (b, b) -> (Maybe Ordering, Maybe Ordering)
circ s i = case i of
  Just (a, b) -> (Just $ compare (a + b) 0, s)
  Nothing -> (Nothing, s)

