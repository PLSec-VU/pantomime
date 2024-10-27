module NoState
  ( obs
  , leak
  , sim
  , adder
  ) where

import UC

{-# ANN adder UCTactic 
  { observation = 'obs
  , leakage = 'leak
  , simulator = 'sim
  , projections = []
  } #-}
adder :: () -> Maybe (Int, Int) -> ((), Maybe Int)
adder _ (Just (a, b)) = ((), Just $ a + b)
adder _ _ = ((), Nothing)

obs :: Maybe Int -> Maybe ()
obs (Just _) = Just ()
obs _ = Nothing

leak :: Maybe (Int, Int) -> Maybe ()
leak (Just _) = Just ()
leak _ = Nothing

sim :: () -> Maybe () -> ((), Maybe ())
sim _ i = ((), i)
