module TwoAdders
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
  , add12
  , obs12
  , sim12
  , proj12
  ) where

import UC


-- | Show that leak1 is a leakage for add1 wrt obs1

-- {-# ANN add1 UC
--   { observation = 'obs1
--   , leakage = 'leak1
--   , simulator = 'sim1
--   , projection = 'proj1
--   } #-}

obs1 :: Maybe Int -> Maybe Bool
obs1 (Just r) = Just (r==0)
obs1 Nothing  = Nothing

sim1 :: () -> Maybe Bool -> ((), Maybe Bool)
sim1 _ o = ((), o)

proj1 :: Int -> (Int, ())
proj1 reg = (reg, ())

add1 :: Int -> Maybe Int -> ( Int , Maybe Int)
add1 reg (Just imm) = (reg + imm , Just (reg + imm))
add1 reg Nothing = (reg , Nothing)

leak1 :: Int -> Maybe Int -> ( Int , Maybe Bool )
leak1 reg (Just imm) = (reg + imm , Just (reg + imm == 0))
leak1 reg _ = (reg , Nothing)

-- | Show that leak2 is a leakage for add2 wrt obs2

-- {-# ANN add2 UC
--   { observation = 'obs2
--   , leakage = 'leak2
--   , simulator = 'sim2
--   , projection = 'proj2
--   } #-}

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing  = False

add2 :: Maybe Int -> (Maybe Int, Maybe Int) -> (Maybe Int, Maybe Int)
add2 _ (Just a, Just b) | a == 0 = (Nothing, Just b)
add2 _ (Just a, Just b) = (Just (a + b), Nothing)
add2 s _ = (Nothing, s)

obs2 :: Maybe Int -> Bool
obs2 = isJust

sim2 :: Bool -> (Maybe Bool , Bool) -> (Bool , Bool)
sim2 _ (Just True, True) = (False, True)
sim2 _ (Just False, True) = (True, False)
sim2 s _ = (False, s)

proj2 :: Maybe Int -> ((), Bool)
proj2 (Just _) = ((), True)
proj2 Nothing    = ((), False)

leak2 :: () -> (Maybe Int , Maybe Int) -> ((), (Maybe Bool , Bool))
leak2 _ (Just a, i2) = ((), (Just (a == 0), isJust i2))
leak2 _ (Nothing, i2) = ((), (Nothing, isJust i2))

-- | Joint proof
-- {-# ANN add12 UC
--   { observation = 'obs12
--   , leakage = 'leak12
--   , simulator = 'sim12
--   , projection = 'proj12
--   } #-}

add12 :: (Int, Maybe Int) -> ( Maybe Int , Maybe Int ) -> ((Int , Maybe Int), Maybe Int)
add12 (s1, s2) (i1, i2) = ((s1', s2'), o2)
    where
        (s1', o1) = add1 s1 i1
        (s2', o2) = add2 s2 (o1, i2)

obs12 :: Maybe Int -> Bool
obs12 = isJust

leak12 :: Int -> (Maybe Int, Maybe Int) -> (Int, (Maybe Bool, Bool))
leak12 reg (i1, i2) = (reg', (o, isJust i2))
    where 
    (reg', o) = leak1 reg i1

sim12 :: Bool -> (Maybe Bool, Bool) -> (Bool, Bool)
sim12 res (i1, i2) = (res', o12)
        where
            (_   , o1 ) = sim1 () i1
            (res', o12) = sim2 res (o1, i2)

proj12 ::  (Int, Maybe Int) -> (Int, Bool)
proj12 (reg, res) = (reg, isJust res)
