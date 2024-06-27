{-# LANGUAGE RankNTypes #-}

module RW
  ( obs
  , example
  -- , generated
  -- , test
  ) where

-- import UC

obs :: Either Int Char -> Either Int ()
obs = \case
  Right _ -> Right ()
  Left i -> Left i

-- {-# ANN example (UC 'ignore) #-}
example :: Maybe Int -> Int -> (Maybe Int, Either Int Char)
example s i = case s of
  Just a -> (Nothing, Left $ a + i)
  _ -> (Just i, Right 'a')

-- generated :: Maybe Int -> Int -> (Maybe Int, Either Int ())
-- generated s i = 
--   (,)
--   @(Maybe Int)
--   @(Either Int ())
--   ( ((case s of
--       Just _ -> \_ -> Nothing
--       _ -> Just) :: forall a. a -> Maybe a)
--     @Int
--     (case s of
--       Just _ -> undefined
--       _ -> i))
--   (case s of
--     Just a -> Left $ a + i
--     _ -> Right ())

-- test :: Maybe Int -> Either Int ()
-- test s =
--   ((case s of
--     Just a -> Left
--     _ -> Right) :: forall a b. a -> Either a b)
--   @Int
--   @()
--   (case s of
--     Just a -> a
--     _ -> ())

-- test :: Maybe Int -> Either Int ()
-- test 
