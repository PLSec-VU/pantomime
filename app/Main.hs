module Main
  ( main,
  addr2,
  addr_obs2,
  leak_sim2
  -- , test
  ) where

import UC
import Types (UCCheck (..))

--- Encoding the simulation proof for 3-adder

ignore :: Maybe Int -> Maybe ()
ignore (Just v) = Just ()
ignore _ = Nothing

-- We only leak timing
leak2 :: (Maybe Int, Maybe Int) -> (Maybe (), Maybe ())
leak2 (a, b) = (ignore a, ignore b)

-- our two input adder
--{-# ANN addr2 (UC 'ignore) #-}
addr2 :: () -> (Maybe Int, Maybe Int) -> ((), Maybe Int)
addr2 _ (Just a, Just b) = ((), Just (a + b))
addr2 _ _ = ((), Nothing)

{-# ANN addr_obs2 (UC 'id) #-}
addr_obs2 :: () -> (Maybe Int, Maybe Int) -> ((), Maybe ())
addr_obs2 s i = let (s1, o) = addr2 s i in (s1, ignore o)
    
sim2 :: () -> (Maybe (), Maybe ()) -> ((), Maybe ())
sim2 _ (Just _, Just _) = ((), Just ())
sim2 _ _ = ((), Nothing)

--{-# ANN leak_sim2 (UCCompare 'addr_obs2)#-}
{-# ANN leak_sim2 (UC 'id) #-}
leak_sim2 :: () -> (Maybe Int, Maybe Int) -> ((), Maybe ())
leak_sim2 s i = sim2 s (leak2 i)

-- observation funciton
obs :: Maybe Int -> Maybe ()
obs = ignore


-- part 2: three adder proof

-- three input adder: composes two two-adders
-- addr3 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe Int)
-- addr3 (s1, s2) ((a, b), c) = ((s1', s2'), abc)
--   where
--     (s1', ab) = addr2 s1 (a,b)
--     (s2', abc) = addr2 s2 (ab, c)


{-------------------  Old stuff ---------------------}

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

-- -- | the annotation (UC 'ignore) means we'll apply ignore as the output projection
-- {-# ANN adder (UC 'ignore) #-}
-- adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
-- adder = \s -> \i -> case s of
--     Just val -> (Nothing, Just val)
--     _        -> case i of
--       Just ab -> case ab of
--        (a, b) -> (Just (a + b), Nothing)
--       Nothing -> (Nothing, Nothing)

-- | Here, we're only applying output projection id
-- {-# ANN before_sproj (UC 'id) #-}
-- before_sproj :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe ())
-- before_sproj = \s -> \i -> case s of
--   Just _ -> (Nothing, Just ())
--   _ -> case i of
--     Just ab -> case ab of
--       (a, b) -> (Just $ a + b, Nothing)
--     _ -> (Nothing, Nothing)

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
