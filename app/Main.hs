{-# LANGUAGE TemplateHaskell #-}
module Main
  ( main
  , adder
  -- , adder''
  -- , test
  -- , testRedundantCase
  ) where

import UC

-- adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
-- adder = \s -> \i -> case s of
--   Just val -> (Nothing, Just val)
--   _ -> case i of
--     Just ab -> case ab of
--       (a, b) -> (Just (a + b), Nothing)
--     Nothing -> (Nothing, Nothing)

-- adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
-- adder s i = case s of
--   Just val -> (Nothing, Just val)
--   _ -> case i of
--     Just ab -> case ab of
--       (a, b) -> (Just (a + b), Nothing)
--     Nothing -> (Nothing, Nothing)

-- {-# ANN adder' UC #-}
-- adder' :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Bool)
-- adder' = oproj ignore circuit
--   where
--     oproj obs impl s i = let (s', o) = impl s i in (s', obs o)

--     ignore (Just v) = Just (v == 0)
--     ignore Nothing = Nothing

--     circuit (Just val) _ = (Nothing, Just val)
--     circuit _ (Just (a, b)) = (Just (a + b), Nothing)
--     circuit _ _ = (Nothing, Nothing)

ignore :: Eq a => Num a => Maybe a -> Maybe Bool
ignore (Just v) = Just (v == 0)
ignore _ = Nothing

{-# ANN adder (UC 'ignore) #-}
adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
adder s i = case s of
  Just val -> (Nothing, Just val)
  _ -> case i of
    Just ab -> case ab of
      (a, b) -> (Just $ a + b, Nothing)
    Nothing -> (Nothing, Nothing)

-- {-# ANN adder' UC #-}
-- adder' :: Maybe Int -> Maybe (Int, Int) -> (Maybe Bool, Maybe Bool)
-- adder' = sproj ignore circuit
--   where
--     sproj proj impl s i = let (s', o) = impl s i in (proj s', o)

--     circuit :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Bool)
--     circuit (Just val) _ = (Nothing, Just (val == 0))
--     circuit _ (Just (a, b)) = (Just (a + b), Nothing)
--     circuit _ _ = (Nothing, Nothing)

-- {-# ANN adder'' UC #-}
-- adder'' :: Maybe Int -> Maybe (Int, Int) -> (Maybe Bool, Maybe Bool)
-- adder'' = sproj' ignore circuit
--   where
--     sproj' proj impl s = impl (proj s)

--     circuit :: Maybe Bool -> Maybe (Int, Int) -> (Maybe Bool, Maybe Bool)
--     circuit (Just val) _ = (Nothing, Just val)
--     circuit _ (Just (a, b)) = (Just (a + b == 0), Nothing)
--     circuit _ _ = (Nothing, Nothing)

-- {-# ANN testRedundantCase UC #-}
-- testRedundantCase :: Int -> Int
-- testRedundantCase x = case x of
--   0 -> x + 1
--   _ -> x + 1

-- {-# ANN adder' UC #-}
-- adder' :: Int -> Int
-- adder' x = (case x of
--   0 -> 5
--   _ -> x)
--   + 1

-- plus1 :: Maybe Int -> Maybe Int
-- plus1 = fmap (+1)

-- {-# ANN test UC #-}
-- test :: Maybe Int -> (Maybe Int, Maybe Int)
-- test y = let plus1 = fmap (+1) in let x = plus1 y in (x, x)

main :: IO ()
main = return ()
