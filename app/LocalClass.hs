module LocalClass
  ( sim
  , circ
  , adder
  , Local (..)
  ) where

-- import UC

-- {-# ANN adder UCTactic 
--   { observation = 'local
--   , leakage = 'local
--   , simulator = 'sim
--   , projections =
--     [ Projection
--       { ignore = 'local
--       , circuit = 'circ
--       }
--     ]
--   } #-}
adder :: Num a => Maybe a -> Maybe (a, a) -> (Maybe a, Maybe a)
adder s i = case i of
  Just (a, b) -> (Just $ a + b, s)
  Nothing -> (Nothing, s)

class Local f where
  local :: f a -> f ()

instance Local Maybe where
  local (Just _) = Just ()
  local _ = Nothing

sim :: Maybe () -> Maybe () -> (Maybe (), Maybe ())
sim s i = (i, s)

circ :: Maybe () -> Maybe (b, b) -> (Maybe (), Maybe ())
circ s i = case i of
  Just (_, _) -> (Just (), s)
  Nothing -> (Nothing, s)

