module NewType
  ( adder

  , State (..)
  , put
  , get

  , (>>=)
  , (>>)
  ) where

import Prelude hiding (Monad (..), Applicative (..))
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
adder s i = swap $ runState (adder' i) s

adder' :: Num a => Maybe (a, a) -> State (Maybe a) (Maybe a)
adder' i = 
  get >>= \s ->
  put (case i of
    Just (a, b) -> Just (a + b)
    Nothing -> Nothing) >>
  pure s

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

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

newtype State s a = State (s -> (a, s))

put :: s -> State s ()
put s = State $ const ((), s)

get :: State s s
get = State $ \s -> (s, s)

runState :: State s a -> s -> (a, s)
runState (State f) = f

(>>=) :: State s a -> (a -> State s b) -> State s b
(State f) >>= g = State $ \s -> do
  let (x, s') = f s
  let (State g') = g x
  g' s'

(>>) :: State s a -> State s b -> State s b
f >> g = f >>= const g

pure :: a -> State s a
pure x = State $ \s -> (x, s)
