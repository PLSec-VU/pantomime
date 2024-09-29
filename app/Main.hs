{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Collapse lambdas" #-}
{-# HLINT ignore "Redundant lambda" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# HLINT ignore "Use lambda-case" #-}
module Main
  ( main
  , adder
  , leak
  , leak_sim2
  , leak_sim3
  , rw4
  , rw5
  , rw2
  ) where

import UC

obs :: Maybe Int -> Maybe ()
obs (Just _) = Just ()
obs _ = Nothing

leak :: Maybe (Int, Int) -> Maybe ()
leak (Just _) = Just ()
leak _ = Nothing

-- sim :: () -> Maybe () -> ((), Maybe ())
-- sim _ i = ((), i)

-- {-# ANN adder UCTactic 
--   { observation = 'obs
--   , leakage = 'leak
--   , simulator = 'sim
--   , projections = []
--   } #-}
-- adder :: () -> Maybe (Int, Int) -> ((), Maybe Int)
-- adder _ (Just (a, b)) = ((), Just $ a + b)
-- adder _ _ = ((), Nothing)

sim :: Maybe () -> Maybe () -> (Maybe (), Maybe ())
sim s i = (i, s)

circ :: Maybe () -> Maybe (Int, Int) -> (Maybe (), Maybe ())
circ s i = case i of
  Just _ -> (Just (), s)
  Nothing -> (Nothing, s)

{-# ANN adder (UCTactic 
  { observation = 'obs
  , leakage = 'leak
  , simulator = 'sim
  , projections =
    [ Projection
      { ignore = 'obs
      , circuit = 'circ
      }
    ]
  }) #-}
adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
adder s i = case i of
  Just (a, b) -> (Just $ a + b, s)
  Nothing -> (Nothing, s)

--- Encoding the simulation proof for 3-adder
-- Part 1: 2-adder is correct wrt description leak2

--{-# ANN addr_obs2 (UC 'id) #-}
addr_obs2 :: () -> (Maybe Int, Maybe Int) -> ((), Maybe ())
addr_obs2 s i = (s1, obs o)
  where
    (s1, o) = addr2 s i

addr2 :: Num a => p -> (Maybe a, Maybe a) -> ((), Maybe a)
addr2 _ (Just a, Just b) = ((), Just (a + b)) 
addr2 _ _ = ((), Nothing)

leak2 :: (Maybe a1, Maybe a2) -> (Maybe (), Maybe ())
leak2 (Just _, Just _) =  (Just (), Just ())
leak2 _ = (Nothing, Nothing)

sim2 :: p -> (Maybe a1, Maybe a2) -> ((), Maybe ())
sim2 _ (Just _, Just _) = ((), Just ()) 
sim2 _ _ = ((), Nothing)

-- check if leak_sim2 and addr_obs2 are equal
{-# ANN leak_sim2 (UCCompare 'addr_obs2)#-}
leak_sim2 :: () -> (Maybe Int, Maybe Int) -> ((), Maybe ())
leak_sim2 s i = sim2 s (leak2 i)

-- Part 2: Three adder proof

-- Three input adder: composes two two-adders
--{-# ANN addr_obs3 (UC 'id) #-}
addr_obs3 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
addr_obs3 (s1, s2) ((a, b), c) = ((s1', s2'), obs abc)
   where
    (s1', ab) = addr2 s1 (a, b)
    (s2', abc) = addr2 s2 (ab, c)

-- check if leak_sim3 and addr_obs3 are equal 
-- non-compositional proof 
{-# ANN leak_sim3 (UCCompare 'addr_obs3)#-}
leak_sim3 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
leak_sim3 (s1, s2) (ab, c) = ((s1', s2'), abc)
  where
    (s1', ab') = sim2 s1 (leak2 ab)
    (s2', abc) = sim2 s2 (leak2 (ab', c))
 

-- Rewrite steps!
-- check if that's the same as addr_obs3
{-# ANN rw2 (UCCompare 'addr_obs3)#-}
rw2 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
rw2 (s1, s2) ((a, b), c) = ((s1', s2'), abc)
   where
    (s1', ab) = addr2 s1 (a, b)
    (s2', abc) = leak_sim2 s2 (ab, c)


-- | Here, we're only applying output projection id
-- {-# ANN before_sproj (UC 'id) #-}
-- beforeSproj :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe ())
-- beforeSproj = \s -> \i -> case s of
--   Just _ -> (Nothing, Just ())
--   _ -> case i of
--     Just ab -> case ab of
--       (a, b) -> (Just $ a + b, Nothing)
--     _ -> (Nothing, Nothing)

-- -- {-# ANN baseOproj UCNorm #-}
-- baseOproj :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Bool)
-- baseOproj = \s -> \i -> case s of
--   Just val -> (Nothing, Just $ val == 0)
--   _ -> case i of
--     Just ab -> case ab of
--       (a, b) -> (Just $ a + b, Nothing)
--     _ -> (Nothing, Nothing)

-- -- {-# ANN weirdSproj UCNorm #-}
-- weirdSproj :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Bool)
-- weirdSproj = 
--   sproj
--   id
--   (\s -> \i -> case s of
--     Just val -> (Nothing, Just $ val == 0)
--     _ -> case i of
--       Just ab -> case ab of
--         (a, b) -> (Just $ a + b, Nothing)
--       _ -> (Nothing, Nothing))

-- So this is one of the inner statements that still contains a reference to
-- an input (that is, both a and b are derivates of the input).
--
-- Given this, how do we rewrite this such that we have a subexpression
-- that leaks as little as possible about s while still retaining equivalent
-- behaviour.
--
-- Somehow, the case factoring seems to give us this, but it doesn't seem to
-- work as nice for terms with differing argument types. It seems like it should
-- be something slightly more fundamental.
--
-- Just food for thought. What we are really looking for here is to have a
-- sort of 'local' leakage function finder. Local in the sense that only
-- considering these branches like this independently is enough to find the
-- final leakage (as we can join leakage).
--
-- The splitting seemed to remove just those parts that were influenced by the
-- input. The position of e.g. the tuple function inside or outside of the leak
-- function seems totally irrelevant; it is something that doesn't give any
-- information here.
-- inner :: Maybe Int -> Int -> Int -> (Maybe Int, Maybe Bool)
-- inner s a b = case s of
--   Nothing -> (,) (Just $ a + b) Nothing
--   Just val -> (,) Nothing (Just $ val == 0)

-- Let's reiterate the leak function that the case factor procedure found when
-- splitting.
--
-- This seems very sensible; we leak two things using the state.
-- 1. Whether the next state is a Nothing or Just (but not it's content)
-- 2. Whether there is output and if it was equal to 0.
--
-- Now the problem we found was that this splitting is not so nice when we have
-- e.g. constructors that take different input types.
--
-- I'm wondering if we could instead of e.g. leaking the next state is Nothing
-- or Just, we can leak them individually?
-- I.e. we would have two expressions (both with a dead branch in their case).
-- One which leaks Just if the state is Just. The other leaks Nothing if the
-- state is Nothing.
--
-- Hmm. On second thought, this wouldn't work; how would the function where these
-- statements are extracted decide which one to use? Wouldn't this information
-- be only available to the state leakage? I'll have to think about this...
--
-- Perhaps the spine would always need case split over the state?
-- found :: Maybe Int -> Int -> Int -> (Maybe Int, Maybe Bool)
-- found s a b =
--   (,)
--   ( (case s of
--       Just _ -> Just
--       _ -> \_ -> Nothing)
--     (a + b))
--   (case s of
--     Just val -> Just $ val == 0
--     _ -> Nothing)

-- We can consider only the state part?
-- smaller :: Maybe Int -> Int -> Int -> Maybe Int
-- smaller s a b = case s of
--   Just _ -> Just (a + b)
--   _ -> Nothing

-- I still feel like we can somehow quantify the input out of there like so?
-- smaller' :: Maybe Int -> Int -> Int -> Maybe Int
-- smaller' s a b = 
--   ((\a' -> \b' -> case s of
--     Just _ -> Just (a' + b')
--     _ -> Nothing) :: forall a. Num a => a -> a -> Maybe a)
--   a
--   b

-- Of course, we could then also just try doing this for the bigger portion?
-- inner' :: Maybe Int -> Int -> Int -> (Maybe Int, Maybe Bool)
-- inner' s a b = 
--   ((\a' -> \b' -> case s of
--     Nothing -> (,) (Just $ a' + b') Nothing
--     Just val -> (,) Nothing (Just $ val == 0)) :: forall a. Num a => a -> a -> (Maybe a, Maybe Bool))
--   a
--   b

-- Full leakage?
-- {-# ANN leak UCNorm #-}
-- leak :: Maybe Int -> ((Maybe Int, Maybe Bool), forall a. Num a => a -> a -> (Maybe a, Maybe Bool))
-- leak s =
--   (,)
--   (case s of
--     Nothing -> (,) Nothing Nothing
--     Just val -> (,) Nothing (Just $ val == 0))
--   (\a' -> \b' -> case s of
--     Nothing -> (,) (Just $ a' + b') Nothing
--     Just val -> (,) Nothing (Just $ val == 0))

-- I guess we should normalize the leakage?
-- leak' :: Maybe Int -> ((Maybe Int, Maybe Bool), forall a. Num a => a -> a -> (Maybe a, Maybe Bool))
-- leak' = \s -> case s of
--   Nothing -> 
--     (,)
--     ( (,)
--       Nothing
--       Nothing)
--     ((\a' -> \b' ->
--       (,)
--       (Just $ a' + b')
--       Nothing) :: forall a. Num a => a -> a -> (Maybe a, Maybe Bool))
--   Just val ->
--     (,)
--     ( (,)
--       Nothing
--       (Just $ val == 0))
--     ((\_ -> \_ ->
--       (,)
--       Nothing
--       (Just $ val == 0)) :: forall a. a -> a -> (Maybe a, Maybe Bool))

-- {-# ANN withExtracted UCNorm #-}
-- withExtracted :: Maybe Int -> Maybe (Int, Int) -> (((Maybe Int, Maybe Bool), forall a. Num a => a -> a -> (Maybe a, Maybe Bool)), Maybe Bool)
-- withExtracted = 
--   sproj
--   (\s -> case s of
--     Nothing ->
--       (,)
--       ( (,)
--         Nothing
--         Nothing)
--       ((\a' -> \b' ->
--         (,)
--         (Just $ a' + b')
--         Nothing) :: forall a. Num a => a -> a -> (Maybe a, Maybe Bool))
--     Just val ->
--       (,)
--       ( (,)
--         Nothing
--         (Just $ val == 0))
--       ((\_ -> \_ ->
--         (,)
--         Nothing
--         (Just $ val == 0)) :: forall a. a -> a -> (Maybe a, Maybe Bool)))
--   (\s -> \i -> case s of
--     Just val -> (Nothing, Just $ val == 0)
--     _ -> case i of
--       Just ab -> case ab of
--         (a, b) -> (Just $ a + b, Nothing)
--       _ -> (Nothing, Nothing))

-- So there is nothing inherently wrong with this leakage function. It is
-- indeed cutting removing parts of the state, and definitely there exists some
-- simulator that only uses the transformed state. The problem is just that
-- there doesn't seem to be a clear algorithmic way of extracting this function
-- once we've applied it as a state projection. At least, I'm not seeing how to
-- get there with this function as a starting state...
-- withExtractedNorm :: Maybe Int -> Maybe (Int, Int) -> (((Maybe Int, Maybe Bool), forall a. Num a => a -> a -> (Maybe a, Maybe Bool)), Maybe Bool)
-- withExtractedNorm = \s -> \i -> case i of
--   Nothing -> case s of
--     Nothing ->
--       (,)
--       ( (,)
--         ( (,)
--           Nothing
--           Nothing)
--         ((\a' -> \b' -> 
--           (,)
--           (Just (a' + b'))
--           Nothing) :: forall a. Num a => a -> a -> (Maybe a, Maybe Bool)))
--       Nothing
--     Just val ->
--       (,)
--       ( (,)
--         ( (,)
--           Nothing
--           Nothing)
--         ((\a' -> \b' -> 
--           (,)
--           (Just (a' + b'))
--           Nothing) :: forall a. Num a => a -> a -> (Maybe a, Maybe Bool)))
--       (Just (val == 0))
--   Just ab -> case ab of
--     (a, b) -> case s of
--       Nothing ->
--         (,)
--         ( (,)
--           ( (,)
--             Nothing
--             (Just $ a + b == 0))
--           ((\_ -> \_ ->
--             (,)
--             Nothing
--             (Just $ a + b == 0)) :: forall a. a -> a -> (Maybe a, Maybe Bool)))
--         Nothing
--       Just val ->
--         (,)
--         ( (,)
--           ( (,)
--             Nothing
--             (Just $ a + b == 0))
--           ((\a' -> \b' ->
--             (,)
--             (Just $ a' + b')
--             Nothing) :: forall a. Num a => a -> a -> (Maybe a, Maybe Bool)))
--         (Just $ val == 0)

-- withExtracted' :: Maybe Int -> Maybe (Int, Int) -> (((Maybe Int, Maybe Bool), forall a. Num a => a -> a -> (Maybe a, Maybe Bool)), Maybe Bool)
-- withExtracted' =
--   sproj'
--   (\s ->
--     (,)
--     (case s of
--       Nothing -> (,) Nothing Nothing
--       Just val -> (,) Nothing (Just $ val == 0))
--     (\a' -> \b' -> case s of
--       Nothing -> (,) (Just $ a' + b') Nothing
--       Just val -> (,) Nothing (Just $ val == 0)))
--   (\s -> \i -> case i of
--     Nothing -> s
--     Just ab -> case ab of
--       (a, b) -> snd s a b)

-- test :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Bool)
-- test s1 i1 = case s1 of
--   Nothing -> case i1 of 
--     Nothing -> (Nothing, Nothing)
--     Just ab -> case ab of
--       (a, b) -> (Just (a + b), Nothing)
--   Just val -> (Nothing, Just (val == 0))

-- test' :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Bool)
-- test' s1 i1 = case i1 of
--   Nothing -> case s1 of
--     Nothing -> (Nothing, Nothing)
--     Just val -> (Nothing, Just (val == 0))
--   Just ab -> case s1 of
--     Nothing -> case ab of
--       (a, b) -> (Just (a + b), Nothing)
--     Just val -> (Nothing, Just (val == 0))

-- case s1 of
--   Nothing -> case i1 of 
--     Nothing -> (Nothing, Nothing)
--     Just ab -> case ab of
--       (a, b) -> (Just (a + b), Nothing)
--   Just val -> (Nothing, Just (val == 0))

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

{-# ANN rw4 (UCCompare 'rw2)#-}
rw4 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
rw4 (s1, s2) ((a, b), c) = ((s1', s2'), abc)
   where
    (s1', ab) = addr2 s1 (a, b)
    ab' = obs ab
    (s2', abc) = sim2 s2 (ab', c)

{-# ANN rw5 (UCCompare 'rw4)#-}
{-# ANN rw5 (UCCompare 'leak_sim3)#-}
rw5 :: ((), ()) -> ((Maybe Int, Maybe Int), Maybe Int) -> (((),()), Maybe ())
rw5 (s1, s2) ((a, b), c) = ((s1', s2'), abc)
   where
    (s1', ab) = leak_sim2 s1 (a, b)
    (s2', abc) = sim2 s2 (ab, c)

main :: IO ()
main = return ()
