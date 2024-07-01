module Main
  ( main
  , adder
  -- , test
  ) where

import UC
-- import Types (UCCheck (..))

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

-- ignore :: Eq a => Num a => Maybe a -> Maybe Bool
-- ignore (Just v) = Just (v == 0)
-- ignore _ = Nothing

ignore :: Maybe Int -> Maybe Bool
ignore (Just v) = Just (v == 0)
ignore _ = Nothing

-- | the annotation (UC 'ignore) means we'll apply ignore as the output projection
{-# ANN adder (UC 'ignore) #-}
adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
adder = \s -> \i -> case s of
    Just val -> (Nothing, Just val)
    _        -> case i of
      Just ab -> case ab of
       (a, b) -> (Just (a + b), Nothing)
      Nothing -> (Nothing, Nothing)

-- | Here, we're only applying output projection id
{-# ANN before_sproj (UC 'id) #-}
before_sproj :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe ())
before_sproj = \s -> \i -> case s of
  Just _ -> (Nothing, Just ())
  _ -> case i of
    Just ab -> case ab of
      (a, b) -> (Just $ a + b, Nothing)
    _ -> (Nothing, Nothing)

-- ignsim :: Maybe Bool -> Maybe (Int, Int) -> (Maybe Bool, Maybe Bool)
-- ignsim s i = case s of
--   Just val -> (Nothing, Just val)
--   _ -> case i of
--     Just ab -> case ab of
--       (a, b) -> (Just $ a + b == 0, Nothing)
--     _ -> (Nothing, Nothing)

-- leak :: Maybe (Int, Int) -> Maybe Bool
-- leak (Just (a, b)) = Just $ a + b == 0
-- leak _ = Nothing

-- sim :: Maybe Bool -> Maybe Bool -> (Maybe Bool, Maybe Bool)
-- sim s i = case s of
--   Just val -> (Nothing, Just val)
--   _ -> case i of
--     Just eq -> (Just eq, Nothing)
--     _ -> (Nothing, Nothing)

-- {-# ANN test UCCheck
--   { ch_obs = 'ignore
--   , ch_impl = 'adder
--   , ch_ignfun = 'ignore
--   , ch_ignsim = 'ignsim
--   , ch_leak = 'leak
--   , ch_sim = 'sim
--   } #-}
-- test :: ()
-- test = ()

-- void :: Maybe a -> Maybe ()
-- void (Just _) = Just ()
-- void _ = Nothing

-- adder2 :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe ())
-- adder2 = Projection.oproj void adder

-- {-# ANN test (UCCompare 'adder2)#-}
-- test :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe ())
-- test s i = case s of
--   Just _ -> (Nothing, Just ())
--   _ -> case i of
--     Just ab -> case ab of
--       (a, b) -> (Just $ a + b, Nothing)
--     Nothing -> (Nothing, Nothing)

main :: IO ()
main = return ()
