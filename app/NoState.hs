module NoState
  ( obs
  , leak
  , sim
  , adder
  , proj
  ) where

-- import UC

-- {-# ANN adder UC
--   { observation = 'obs
--   , leakage = 'leak
--   , simulator = 'sim
--   , projection = 'proj
--   } #-}
adder :: () -> Maybe (Int, Int) -> ((), Maybe Int)
adder _ (Just (a, b)) = ((), Just $ a + b)
adder _ _ = ((), Nothing)

obs :: Maybe Int -> Maybe ()
obs (Just _) = Just ()
obs _ = Nothing

leak :: () -> Maybe (Int, Int) -> ((), Maybe ())
leak _ (Just _) = ((), Just ())
leak _ _ = ((), Nothing)

sim :: () -> Maybe () -> ((), Maybe ())
sim _ i = ((), i)

proj :: () -> ((), ())
proj _ = ((), ())
