module Projection
  ( Circuit
  , oproj
  , sproj
  , sproj'
  , iproj
  ) where

type Circuit s i o = (s -> i -> (s, o))

-- oproj :: (o -> o') -> (s -> i -> (s', o)) -> (s -> i -> (s', o')) 
oproj :: (o -> o') -> Circuit s i o -> Circuit s i o'
oproj obs impl s i = let (s', o) = impl s i in (s', obs o)

sproj :: (s -> s') -> Circuit s i o -> (s -> i -> (s', o))
sproj obs impl s i = let (s', o) = impl s i in (obs s', o)

sproj' :: (s -> s') -> Circuit s' i o -> (s -> i -> (s', o))
sproj' obs impl s = impl (obs s)

iproj :: (i -> i') -> Circuit s i' o -> Circuit s i o
iproj leak sim s i = sim s $ leak i
