module Monad
  ( obs
  , leak
  , sim
  , proj
  , adder
  ) where

import Control.Monad.State (MonadState, put, get, runState)
import UC

{-# ANN adder UC
  { observation = 'obs
  , leakage = 'leak
  , simulator = 'sim
  , projection = 'proj
  } #-}
-- {-# ANN adder UCNorm #-}
adder :: Num a => Maybe a -> Maybe (a, a) -> (Maybe a, Maybe a)
adder s i = swap $ runState (adder' i) s

adder' :: Num a => MonadState (Maybe a) m => Maybe (a, a) -> m (Maybe a)
adder' i = do
  s <- get
  put $ case i of
    Just (a, b) -> Just (a + b)
    Nothing -> Nothing
  pure s

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

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
