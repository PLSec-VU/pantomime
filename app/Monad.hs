module Monad
  ( obs
  , leak
  , sim
  , circ
  , adder
  , test
  ) where

import Control.Monad.State (State, put, get, runState)
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
-- {-# ANN adder UCNorm #-}
adder :: Num a => Maybe a -> Maybe (a, a) -> (Maybe a, Maybe a)
adder s i = swap $ runState (adder' i) s

-- {-# ANN adder UCNorm #-}
-- adder :: Num a => Maybe a -> Maybe (a, a) -> (Maybe a, Maybe a)
-- adder s i = runState (adder' i) s

-- adder' :: Num a => MonadState (Maybe a) m => Maybe (a, a) -> m (Maybe a)
adder' :: Num a => Maybe (a, a) -> State (Maybe a) (Maybe a)
adder' i = do
  s <- get
  put $ case i of
    Just (a, b) -> Just (a + b)
    Nothing -> Nothing
  pure s

-- {-# ANN test UCNorm #-}
test :: Num a => a -> State a a
test x = do
  put $ x + 1
  pure x

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

-- TODO: Try this with newtype. It introduce a lot of casts, which we should
-- be able to deal with!
-- newtype State s a = State (s -> (a, s))
--   deriving Functor

-- instance Applicative (State s) where
--   pure x = State $ \s -> (x, s)

--   (State f) <*> (State g) = State $ \s -> do
--     let (h, s') = f s
--     let (x, s'') = g s'
--     (h x, s'')

--   -- {-# INLINE (*>) #-}
--   a1 *> a2 = (id <$ a1) <*> a2

-- instance Monad (State s) where
--   (State f) >>= g = State $ \s -> do
--     let (x, s') = f s
--     let (State g') = g x
--     g' s'

--   -- {-# INLINE (>>) #-}
--   (>>) = (*>)

-- put :: s -> State s ()
-- put s = State $ const ((), s)

-- get :: State s s
-- get = State $ \s -> (s, s)

-- runState :: State s a -> s -> (a, s)
-- runState (State f) = f
