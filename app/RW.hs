{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module RW
  ( obs
  , example
  , test
  , generated
  -- , generated
  -- , test
  ) where

-- import UC
-- import Projection

obs :: Either Int Char -> Either Int ()
obs = \case
  Right _ -> Right ()
  Left i -> Left i

-- {-# ANN example (UC 'obs) #-}
example :: Maybe Int -> Int -> (Maybe Int, Either Int Char)
example s i = case s of
  Just a -> (Nothing, Left $ a + i)
  _ -> (Just i, Right 'a')

generated :: Maybe Int -> Int -> (Maybe Int, Either Int ())
generated s i = case s of
  Just a -> (Nothing, Left $ a + i)
  _ -> (Just i, Right ())

-- adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
-- adder s i = case s of
--   Just val -> (Nothing, Just val)
--   _ -> case i of
--     Just ab -> case ab of
--       (a, b) -> (Just $ a + b, Nothing)
--     _ -> (Nothing, Nothing)

-- generated' :: Maybe Int -> Int -> (Maybe Int, Either Int ())
-- generated' s i = 
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

-- generated' :: Maybe Int -> Int -> (Maybe Int, Either Int ())
-- generated' s i = 
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

test :: Maybe Int -> Either Int ()
test s = case s of
  Just a -> Left a
  _ -> Right ()

-- -- Maybe we join with the split as much as we can? For example, now we split
-- -- just the unit. The type applications on Left and Right we could join as
-- -- they're of the same kind. For terms we would join them if they are of the
-- -- same type.
-- test0 :: Maybe Int -> Either Int ()
-- test0 s =
--   (case s of
--     Just a -> \_ -> Left @Int @() a
--     _ -> Right @Int @())
--   (case s of
--     Just a -> undefined
--     _ -> ())

-- -- We can remove the case on the unit: undefined should coerce to any other
-- -- branch, so this is just a redudant case!
-- test1 :: Maybe Int -> Either Int ()
-- test1 s =
--   (case s of
--     Just a -> \_ -> Left @Int @() a
--     _ -> Right @Int @())
--   ()

-- -- Now the problem is that the Just branch is not an application anymore...
-- -- This split doesn't really seem to work :/
-- test2 :: Maybe Int -> Either Int ()
-- test2 = undefined

-- -- What if we push the lambda outside of the case?
-- test0' :: Maybe Int -> Either Int ()
-- test0' s =
--   (\u -> case s of
--     Just a -> Left @Int @() a
--     _ -> Right @Int @() u)
--   (case s of
--     Just a -> undefined
--     _ -> ())

-- -- Let's again remove the redundant case on the unit.
-- test1' :: Maybe Int -> Either Int ()
-- test1' s =
--   (\u -> case s of
--     Just a -> Left @Int @() a
--     _ -> Right @Int @() u)
--   ()

-- -- We can now again do the transformation? I guess the initial idea was to get
-- -- rid of the applications? This still retains them, but moves the leakage part
-- -- away. Now it's just the usage that is retained?
-- test2' :: Maybe Int -> Either Int ()
-- test2' s =
--   (\u -> 
--     (\a -> case s of
--       Just _ -> Left @Int @() a
--       _ -> Right @Int @() u)
--     (case s of
--       Just a -> a
--       _ -> undefined))
--   ()

-- -- What about the original example we had (where the observation tells us
-- -- whether the output is zero).
-- rwN :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Bool)
-- rwN = \s -> \i -> case s of
--   Just val -> (,) Nothing (Just ((==) val 0))
--   _ -> case i of
--     Just ab -> case ab of
--       (,) a b -> (,) (Just ((+) a b)) Nothing
--     _ -> (,) Nothing Nothing

-- I guess one question now is; what is the point of grouping? Why would it be
-- somehow better to group two terms of the same type? Their leakage ought the
-- be the same whether they were grouped or not?
--
-- Similarly, do we care to disentangle all terms? I guess we only really need
-- to disentangle terms that depend on the state from terms that depend on the
-- input. Perhaps we can use this process, but only on terms that contain the
-- state/input (depending on the goal) as free variables.

-- test' :: Maybe Int -> Either Int ()
-- test' s =
--   (\a -> case s of
--     Just _ -> Left a
--     _ -> Right ())
--   (case s of
--     Just a -> a
--     _ -> undefined)

-- test :: Maybe Int -> Either Int ()
-- test 
