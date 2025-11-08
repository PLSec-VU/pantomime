module Two2Adders
  ( obs2
  , leak2
  , sim2
  , proj2
  , add2
  , obs1
  , leak1
  , sim1
  , proj1
  , leak3
  , sim3
  , proj3
  , repeat1
  , double
  , leak4
  , sim4
  , proj4
  , shift
  -- , leak5
  -- , sim5
  -- , proj5
  ) where

-- import UC
import Prelude hiding (seq)

-- | Show that leak2 is a leakage for add2 wrt obs2

-- {-# ANN add2 UC
--   { observation = 'obs2
--   , leakage = 'leak2
--   , simulator = 'sim2
--   , projection = 'proj2
--   } #-}

-- Second adder
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


-- First adder

-- {-# ANN add2 UC
--   { observation = 'obs1
--   , leakage = 'leak1
--   , simulator = 'sim1
--   , projection = 'proj1
--   } #-}

obs1 :: Maybe Int -> Maybe Bool
obs1 (Just res) = Just (res == 0)
obs1 Nothing = Nothing

l1 :: (Maybe Int , Maybe Int) -> Maybe (Bool, Bool)
l1 (Just a, Just b) = Just (a==0, a+b ==0)
l1 _ = Nothing

leak1 :: () -> (Maybe Int , Maybe Int) -> ((), (Maybe (Bool, Bool)))
leak1 _ i = ((), l1 i)

sim1 :: Maybe Bool -> (Maybe (Bool, Bool)) -> (Maybe Bool, Maybe Bool)
sim1 _ (Just (True, isZero)) = (Nothing, Just isZero)
sim1 _ (Just (False, isZero)) = (Just isZero, Nothing)
sim1 isZero _  = (Nothing, isZero)

proj1 :: Maybe Int -> ((), Maybe Bool)
proj1 (Just res) = ((), Just $ res == 0)
proj1 Nothing = ((), Nothing)

-- Lemma repeat
-- {-# ANN repeat1 UC
--   { observation = 'obs2
--   , leakage = 'leak3
--   , simulator = 'sim3
--   , projection = 'proj3
--   } #-}

-- repeat saves the old input and repeats on stall
repeat1 :: Maybe Int -> (Maybe Int, Bool) -> (Maybe Int, Maybe Int)
repeat1 (Just old) (_, True) = (Nothing, Just old)
repeat1 _ (new, _) = (new, new)

leak3 :: () -> (Maybe Int, Bool) -> ((), (Bool, Bool))
leak3 _ (i, b) = ((), (isJust i, b))

sim3 :: Bool -> (Bool, Bool) -> (Bool, Bool)
sim3 True (_, True) = (False, True)
sim3 _ (new, _) = (new, new)

proj3 :: Maybe Int -> ((), Bool)
proj3 i = ((), isJust i)

-- Lemma double
-- {-# ANN double UC
--   { observation = 'obs4
--   , leakage = 'leak4
--   , simulator = 'sim4
--   , projection = 'proj4
--   } #-}

double :: () -> Maybe Int -> ((), (Maybe Int, Bool))
double _ i = ((), (i, isJust i))

obs4 :: (Maybe Int, Bool) -> (Bool, Bool)
obs4 (i, b) = (isJust i, b)

leak4 :: () -> Maybe Int -> ((), Bool)
leak4 _ i = ((), isJust i)

sim4 :: () -> Bool -> ((), (Bool, Bool))
sim4 _ b = ((), (b, b))

proj4 :: () -> ((),())
proj4 _ = ((),())

-- lemma shift
-- {-# ANN shift UC
--   { observation = 'obs5
--   , leakage = 'leak5
--   , simulator = 'sim5
--   , projection = 'proj5
--   } #-}

shift :: () -> ((Maybe Int, Maybe Int, Maybe Int), Bool) -> ((), ((Maybe Int, Maybe Int), (Maybe Int, Bool)))
shift _ ((a,b,c), d) = ((), ((a,b),(c,d)))

obs5 :: ((Maybe Int, Maybe Int), (Maybe Int, Bool)) -> (Maybe (Bool, Bool), (Bool, Bool))
obs5 ((a,b),(c, d)) = (l1 (a, b), (isJust c, d))

leak5 :: () -> ((Maybe Int, Maybe Int, Maybe Int), Bool) -> ((), (Maybe (Bool, Bool), Bool, Bool))
leak5 _ ((a,b,c),d) = ((), (l1 (a, b), isJust c, d))

sim5 :: () -> (Maybe (Bool, Bool), Bool, Bool) -> ((), (Maybe (Bool, Bool), (Bool, Bool)))
sim5 _ (a, b, c) = ((), (a,(b, c)))

proj5 :: () -> ((),())
proj5 _ = ((),())

---------------------------
--- Circuit Combinators ---
---------------------------
type Circ s i o = s -> i -> (s, o)

seq :: Circ s1 i i1 -> Circ s2 i1 o -> Circ (s1,s2) i o
c1 `seq` c2 = \(s1, s2) i -> 
  let (s1', i1) = c1 s1 i
      (s2', o) = c2 s2 i1
  in ((s1',s2'), o)
  
par :: Circ s1 i1 o1 -> Circ s2 i2 o2 -> Circ (s1, s2) (i1,i2) (o1,o2)
c1 `par` c2 = \(s1,s2) (i1, i2) ->
  let (s1', o1) = c1 s1 i1
      (s2', o2) = c2 s2 i2
  in ((s1', s2'), (o1, o2))

loop :: Circ s (i, l) (o, l) -> Circ (s, l) i o
loop c = \(s, l) i -> 
  let (s', (o, l')) = c s (i, l)
  in ((s, l'), o)

two2adders = loop $ shift `seq` (add2 `par` repeat1) `seq` add2 `seq` double

