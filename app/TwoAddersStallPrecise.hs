module TwoAddersStallPrecise
  ( obs1
  , leak1
  , sim1
  , proj1
  , add1
  , obs2
  , leak2
  , sim2
  , proj2
  , add2
  --, test
--   , add12
--   , obs12
--   , sim12
--   , proj12
  ) where

-- import Test.QuickCheck
import Projection
import UC

-- | Show that leak1 is a leakage for add1 wrt obs1

-- {-# ANN add1 UC
--   { observation = 'obs1
--   , leakage = 'leak1
--   , simulator = 'sim1
--   , projection = 'proj1
--   } #-}

add1 :: Int -> (Bool, Maybe Int) -> (Int, Maybe Int)
add1 reg (stall, Just imm)
    | stall     = (reg, Nothing)     
    | otherwise = (reg + imm, Just (reg + imm))
add1 reg (_, Nothing) = (reg, Nothing) 

leak1 :: Int -> (Bool, Maybe Int) -> (Int, Maybe Bool)
leak1 reg (stall, Just imm)  
    | stall     = (reg, Nothing)     
    | otherwise = (reg + imm, Just (reg + imm==0))
leak1 reg (_, Nothing) = (reg, Nothing) 

obs1 :: Maybe Int -> Maybe Bool
obs1 (Just r) = Just (r==0)
obs1 Nothing  = Nothing

sim1 :: () -> Maybe Bool -> ((), Maybe Bool)
sim1 _ o1 = ((), o1)

proj1 :: Int -> (Int, ())
proj1 reg = (reg, ())

-- {-# ANN add2 UC
--   { observation = 'obs2
--   , leakage = 'leak2
--   , simulator = 'sim2
--   , projection = 'proj2
--   } #-}

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing  = False

-- | Show that leak2 is a leakage for add2 wrt obs2

add2 :: Maybe Int -> (Maybe Int, Maybe Int) -> (Maybe Int, (Maybe Int, Bool))
add2 _ (Just a, Just b) | a == 0 = (Nothing, (Just b, False))
add2 _ (Just a, Just b) = (Just (a + b), (Nothing, True))
add2 s _    = (Nothing, (s, False))

-- | is there an output, and do we stall?
obs2 :: (Maybe Int, Bool) -> (Bool, Bool)
obs2 (Just _, stall) = (True, stall)
obs2 (Nothing, stall) = (False, stall)

leak2 :: () -> (Maybe Int, Maybe Int) -> ((), (Maybe Bool, Bool))
leak2 _ (Just res, i2) = ((), (Just $ res == 0,  isJust i2))
leak2 _ (Nothing, i2) = ((), (Nothing,  isJust i2))


sim2 :: Bool -> (Maybe Bool , Bool) -> (Bool , (Bool, Bool))
sim2 _ (Just True, True) = (False, (True, False))
sim2 _ (Just False, True) = (True, (False, True))
sim2 s _ = (False, (s, False))

proj2 :: Maybe Int -> ((), Bool)
proj2 (Just res) = ((), True)
proj2 Nothing    = ((), False)

-- -- Proof of the composed circuit

-- {-# ANN add12 UC
--   { observation = 'obs12
--   , leakage = 'leak12
--   , simulator = 'sim12
--   , projection = 'proj12
--   } #-}

add12 :: (Int, Maybe Int, Bool) -> (Maybe Int, Maybe Int) -> ((Int, Maybe Int, Bool), Maybe Int)
add12 (s1, s2, stalled) (i1, i2) = ((s1', s2', stall), o2)
    where
        (s1', o1) = add1 s1 (stalled, i1)
        (s2', (o2, stall)) = add2 s2 (o1, i2)

-- -- | Overall observation is just timing
obs12 :: Maybe Int -> Bool
obs12 = isJust


-- | leak12 needs to keep track of the accurate register state of add1 (to leak when it will be 0).
-- | for that, it needs to know when the overall circuit will stall.

-- leak12 :: (Int, Bool) -> (Maybe Int, Maybe Int) -> ((Int, Bool), (Maybe Bool, Bool))
-- leak12 (reg, stall) (i1, i2) = case (stall, i1) of
--     (True, _)         -> ((reg, False), (Nothing, isJust i2))
--     (False, Just imm) -> ((reg + imm, i2 /= Nothing && reg + imm/=0), (Just (reg + imm==0), isJust i2))
--     (False, Nothing)  -> ((reg, False), (Nothing, isJust i2))

-- leak12 :: (Int, Bool) -> (Maybe Int, Maybe Int) -> ((Int, Bool), (Maybe Bool, Bool))
-- leak12 (reg, stall) (i1, i2) = case (stall, i1) of
--     (True, _)         -> ((reg, False), (Nothing, isJust i2))
--     (False, Just imm) -> ((reg + imm, i2 /= Nothing && reg + imm/=0), (Just (reg + imm==0), isJust i2))
--     (False, Nothing)  -> ((reg, False), (Nothing, isJust i2))


-- sim12 :: ((), Bool, Bool)  -> (Maybe Bool, Bool) -> (((), Bool, Bool), Bool)
-- sim12 (s1, s2, stalled) (l1, l2) = ((s1', s2', stall), o2)     
--     where
--     (s1', o1) = sim1 s1 (stalled, l1)
--     (s2', (o2, stall)) = sim2 s2 (o1, l2)

-- proj12 :: (Int, Maybe Int, Bool) -> ((Int, Bool), ((), Bool, Bool))
-- proj12 (s1, s2, stalled) = ((s1, stalled), ((), isJust s2, stalled))

-- -- ----------------------------------------------------------------------
-- -- | Test corner -- we can check our theorems using quick-check
-- -------------------------------------------------------------------------
-- mealy :: (s -> i -> (s, o)) -> s -> [i] -> [o]
-- mealy _ _ [] = []
-- mealy f s (x:xs) =
--     let (s', o) = f s x
--     in o : mealy f s' xs

-- -- | alps * operator  
-- seqc :: (s1 -> i1 -> (s1, o)) -> (s2 -> o -> (s2, o2)) -> (s1,s2) -> i1 -> ((s1,s2), o2)
-- seqc c1 c2 (s1,s2) i = ((s1',s2'), o2)
--     where
--       (s1', o1) = c1 s1 i
--       (s2', o2) = c2 s2 o1 

-- theorem :: [(Maybe Int, Maybe Int)] -> Bool
-- theorem ins = mealy add12_obs (0, Nothing, False) ins == mealy leak12_sim ((0,False),((), False, False)) ins
--     where 
--         add12_obs s i =  let (s', o) = add12 s i in (s', obs12 o)
--         leak12_sim = seqc leak12 sim12

-- test = do
--     quickCheckWith stdArgs { maxSuccess = 1000000 } theorem
--     let ins = [(Just 1,Nothing),(Just 0,Just 0),(Nothing,Nothing)]
--     putStrLn "Implementation"
--     putStrLn $ show $ mealy add12_obs (0, Nothing, False) ins
--     putStrLn "Simulator"
--     putStrLn $ show $ mealy leak12_sim ((0,False),((), False, False)) ins
--   where 
--       add12_obs s i =  let (s', o) = add12 s i in (s', obs12 o)
--       leak12_sim = seqc leak12 sim12
