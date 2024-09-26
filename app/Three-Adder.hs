module Main
  ( main,
  addr_obs2,
  leak_sim2,
  addr_obs3,
  leak_sim3,
  rw2,
  rw4,
  rw5
  -- , test
  ) where

import UC
import Types (UCCheck (..))

--- Encoding the simulation proof for 3-adder
-- Part 1: 2-adder is correct wrt description leak2

{-# ANN addr_obs2 (UC 'id) #-}
addr_obs2 :: () -> (Maybe Int, Maybe Int) -> ((), Maybe ())
addr_obs2 s i = (s1, ignore o)
    where
  (s1, o) = addr2 s i
  ignore (Just _) = Just ()
  ignore _ = Nothing
  addr2 _ (Just a, Just b) = ((), Just (a + b)) 
  addr2 _ _ = ((), Nothing)
    
-- check if leak_sim2 and addr_obs2 are equal
{-# ANN leak_sim2 (UCCompare 'addr_obs2)#-}
leak_sim2 :: () -> (Maybe Int, Maybe Int) -> ((), Maybe ())
leak_sim2 s i = sim2 s (leak2 i)
  where
    -- leakage description
    leak2 (Just _, Just _) =  (Just (), Just ())
    leak2 _ = (Nothing, Nothing)
    sim2 _ (Just _, Just _) = ((), Just ()) 
    sim2 _ _ = ((), Nothing)

-- Part 2: Three adder proof

-- Three input adder: composes two two-adders
--{-# ANN addr_obs3 (UC 'id) #-}
addr_obs3 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
addr_obs3 (s1, s2) ((a, b), c) = ((s1', s2'), ignore abc)
   where
    (s1', ab) = addr2 s1 (a, b)
    (s2', abc) = addr2 s2 (ab, c)
    addr2 _ (Just x, Just y) = ((), Just (x + y)) 
    addr2 _ _ = ((), Nothing)
    ignore (Just _) = Just ()
    ignore _ = Nothing

-- check if leak_sim3 and addr_obs3 are equal 
-- non-compositional proof 
{-# ANN leak_sim3 (UCCompare 'addr_obs3)#-}
leak_sim3 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
leak_sim3 (s1, s2) (ab, c) = ((s1', s2'), abc)
  where
    (s1', ab') = sim2 s1 (leak2 ab)
    (s2', abc) = sim2 s2 (leak2 (ab', c))
    sim2 _ (Just _, Just _) = ((), Just ()) 
    sim2 _ _ = ((), Nothing)
    leak2 (Just _, Just _) =  (Just (), Just ())
    leak2 _ = (Nothing, Nothing)
  

-- Rewrite steps!
-- check if that's the same as addr_obs3
{-# ANN rw2 (UCCompare 'addr_obs3)#-}
rw2 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
rw2 (s1, s2) ((a, b), c) = ((s1', s2'), abc)
   where
    (s1', ab) = addr2 s1 (a, b)
    (s2', abc) = leak_sim2 s2 (ab, c)
    addr2 _ (Just a, Just b) = ((), Just (a + b)) 
    addr2 _ _ = ((), Nothing)
    leak2 (Just a, Just b) =  (Just (), Just ())
    leak2 _ = (Nothing, Nothing)
    sim2 _ (Just _, Just _) = ((), Just ()) 
    sim2 _ _ = ((), Nothing)
    leak_sim2 s i = sim2 s (leak2 i)

{-# ANN rw4 (UCCompare 'rw2)#-}
rw4 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
rw4 (s1, s2) ((a, b), c) = ((s1', s2'), abc)
   where
    (s1', ab) = addr2 s1 (a, b)
    ab' = ignore ab
    (s2', abc) = sim2 s2 (ab', c)
    addr2 _ (Just a, Just b) = ((), Just (a + b)) 
    addr2 _ _ = ((), Nothing)
    sim2 _ (Just _, Just _) = ((), Just ()) 
    sim2 _ _ = ((), Nothing)
    ignore (Just v) = Just ()
    ignore _ = Nothing

{-# ANN rw5 (UCCompare 'rw4)#-}
{-# ANN rw5 (UCCompare 'leak_sim3)#-}
rw5 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
rw5 (s1, s2) ((a, b), c) = ((s1', s2'), abc)
   where
    (s1', ab) = leak_sim2 s1 (a, b)
    (s2', abc) = sim2 s2 (ab, c)
    addr2 _ (Just a, Just b) = ((), Just (a + b)) 
    addr2 _ _ = ((), Nothing)
    sim2 _ (Just _, Just _) = ((), Just ()) 
    sim2 _ _ = ((), Nothing)
    leak2 (Just a, Just b) =  (Just (), Just ())
    leak2 _ = (Nothing, Nothing)
    leak_sim2 s i = sim2 s (leak2 i)

main :: IO ()
main = return ()
