module ClassInline
  ( sim
  , circ
  , adder
  ) where

-- import UC
-- import Control.Monad (void)

-- {-# ANN adder UCTactic 
--   { observation = 'void
--   , leakage = 'void
--   , simulator = 'sim
--   , projections =
--     [ Projection
--       { ignore = 'void
--       , circuit = 'circ
--       }
--     ]
--   } #-}
adder :: Num a => Maybe a -> Maybe (a, a) -> (Maybe a, Maybe a)
adder s i = case i of
  Just (a, b) -> (Just $ a + b, s)
  Nothing -> (Nothing, s)

sim :: Maybe () -> Maybe () -> (Maybe (), Maybe ())
sim s i = (i, s)

circ :: Maybe () -> Maybe (b, b) -> (Maybe (), Maybe ())
circ s i = case i of
  Just (a, b) -> (Just (), s)
  Nothing -> (Nothing, s)

