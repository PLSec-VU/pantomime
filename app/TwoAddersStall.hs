module TwoAddersStall
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
  -- , add12
  -- , obs12
  -- , sim12
  -- , proj12
  ) where

import Test.QuickCheck
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

-- | we only leak the new register value if we're not stalled
leak1 :: Int -> (Bool, Maybe Int) -> (Int, Maybe Bool)
leak1 reg (False, Just imm) = (reg + imm, Just (reg + imm == 0))
leak1 reg (_,_) = (reg, Nothing)

obs1 :: Maybe Int -> Maybe Bool
obs1 (Just r) = Just (r==0)
obs1 Nothing  = Nothing

sim1 :: () -> Maybe Bool -> ((), Maybe Bool)
sim1 _ o = ((), o)

proj1 :: Int -> (Int, ())
proj1 reg = (reg, ())


{-# ANN add2 UC
  { observation = 'obs2
  , leakage = 'leak2
  , simulator = 'sim2
  , projection = 'proj2
  } #-}


isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing  = False

-- | Show that leak2 is a leakage for add2 wrt obs2

add2 :: Maybe Int -> (Maybe Int, Maybe Int) -> (Maybe Int, (Maybe Int, Bool))
add2 _ (Just 0, Just b) = (Nothing, (Just b, False))
add2 _ (Just a, Just b) = (Just (a + b), (Nothing, True))
add2 s _    = (Nothing, (s, False))

-- | or do we just leak whether there's an output? 
obs2 :: (Maybe Int, Bool) -> (Bool, Bool)
obs2 (Just _, stall) = (True, stall)
obs2 (Nothing, stall) = (False, stall)

leak2 :: () -> (Maybe Int , Maybe Int) -> ((), (Maybe Bool, Maybe ()))
leak2 _ (Just a, Just b) = ((), (Just (a == 0),  Just ()))
leak2 _ _ = ((), (Nothing, Nothing))

sim2 :: Bool -> (Maybe Bool , Maybe ()) -> (Bool , (Bool, Bool))
sim2 _ (Just True, Just ()) = (False, (True, False))
sim2 _ (Just False, Just ()) = (True, (False, True))
sim2 s _ = (False, (s, False))

proj2 :: Maybe Int -> ((), Bool)
proj2 (Just res) = ((), True)
proj2 Nothing    = ((), False)


-- | Test corner
mealy :: (s -> i -> (s, o)) -> s -> [i] -> [o]
mealy _ _ [] = []
mealy f s (x:xs) =
    let (s', o) = f s x
    in o : mealy f s' xs

seqc :: (s1 -> i1 -> (s1, o)) -> (s2 -> o -> (s2, o2)) -> (s1,s2) -> i1 -> ((s1,s2), o2)
seqc c1 c2 (s1,s2) i = ((s1',s2'), o2)
    where
      (s1', o1) = c1 s1 i
      (s2', o2) = c2 s2 o1 

theorem :: [(Maybe Int, Maybe Int)] -> Bool
theorem ins = mealy add2_obs Nothing ins == mealy leak2_sim ((), False) ins
    where 
        add2_obs s i =  let (s', o) = add2 s i in (s', obs2 o)
        leak2_sim = seqc leak2 sim2

test = do
    quickCheckWith stdArgs { maxSuccess = 1000000 } theorem