module Poly2
  ( adder
  , obs
  , leak
  , sim
  , proj
  ) where

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

obs :: Num a => Ord a => Maybe a -> Maybe Ordering
obs (Just x) = Just $ compare x 0
obs _ = Nothing

leak :: Ord a => Num a => () -> Maybe (a, a) -> ((), Maybe Ordering)
leak _ (Just (x, y)) = ((), Just $ compare (x + y) 0)
leak _ _ = ((), Nothing)

sim :: Maybe Ordering -> Maybe Ordering -> (Maybe Ordering, Maybe Ordering)
sim s i = (i, s)

proj :: Num a => Ord a => Maybe a -> ((), Maybe Ordering)
proj = (\s -> ((), s)) . obs
