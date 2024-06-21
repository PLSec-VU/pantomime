{-# LANGUAGE TemplateHaskell #-}
module Main
  ( main
  --, adder
  --, before_sproj
  --, sproj_left
  --, sproj_right
   , after_sproj
  , sim 
  ) where

import UC
----------------------------
-- | Helper functions
----------------------------
ignore :: Maybe a -> Maybe ()
ignore = \i -> case i of
  (Just _) -> Just ()
  _        -> Nothing

-- ------------------------------------------------------------------------  
-- {-- Rewrite step 1: initial to just before the state projection.  --}
-- ------------------------------------------------------------------------  

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
      (a, b) -> (Just (a + b), Nothing)
    Nothing -> (Nothing, Nothing)

------------------------------------------------------------------------------------------------------  
{-- Rewrite step 2: this is the rewrite we need to show in order to apply the state projection.  --}
------------------------------------------------------------------------------------------------------    

{-# ANN sproj_left (UC 'id) #-}
sproj_left :: Maybe Int -> Maybe (Int, Int) -> (Maybe (), Maybe ())
sproj_left = sproj ignore go
  where
    sproj mask impl s i =  case impl s i of (s', o) -> (mask s', o)
    -- 
    ignore (Just _) = Just ()
    ignore _ = Nothing
    --
    go = \s -> \i -> case s of
      Just _ -> (Nothing, Just ())
      _   -> case i of
        Just ab -> case ab of
          (a, b) -> (Just (a + b), Nothing)
        Nothing -> (Nothing, Nothing)


{-# ANN sproj_right (UC 'id) #-}
sproj_right :: Maybe Int -> Maybe (Int, Int) -> (Maybe (), Maybe ())
sproj_right s i = go (ignore s) i
  where
    --
    ignore (Just _) = Just ()
    ignore _ = Nothing
    --
    go = \s -> \i -> case s of
      Just _ -> (Nothing, Just ())
      _   -> case i of
        Just ab -> case ab of
          (a, b) -> (Just (), Nothing)
        Nothing -> (Nothing, Nothing)

-- ----------------------------------------------------------------------------------------------  
-- {-- Rewrite step 3: after the state projection to leakage description + simulator.  --}
-- ----------------------------------------------------------------------------------------------  

{-# ANN after_sproj (UC 'id) #-}
after_sproj :: Maybe () -> Maybe (Int, Int) -> (Maybe (), Maybe ())
after_sproj = (\s -> \i -> case s of
  Just val -> (Nothing, Just ())
  _ -> case i of
    Just ab -> case ab of
      (a, b) -> (ignore $ Just (a, b), Nothing)
    Nothing -> (Nothing, Nothing))
  where 
    ignore (Just _) = Just ()
    ignore _ = Nothing

{-# ANN sim (UC 'id) #-}
sim :: Maybe () -> Maybe (Int, Int) -> (Maybe (), Maybe ())
sim s i = go s (ignore i)
  where
  go = \s -> \i -> case s of
    Just () -> (Nothing, Just ())
    _       -> case i of
      Just () -> (Just (), Nothing)
      Nothing -> (Nothing, Nothing)

  ignore (Just _) = Just ()
  ignore _ = Nothing


main :: IO ()
main = return ()
