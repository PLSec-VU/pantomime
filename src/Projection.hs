module Projection
  ( Circuit
  , oproj
  , sproj
  , sproj'
  , iproj
  , composeI
  , composeS
  ) where

type Circuit s i o = (s -> i -> (s, o))

oproj :: (o -> o') -> Circuit s i o -> Circuit s i o'
oproj obs impl s i = do
  let (s', o) = impl s i
  (s', obs o)

sproj :: (s -> s') -> Circuit s i o -> (s -> i -> (s', o))
sproj obs impl s i = do
  let (s', o) = impl s i
  (obs s', o)

sproj' :: (s -> s') -> Circuit s' i o -> (s -> i -> (s', o))
sproj' obs impl s = impl (obs s)

iproj :: Circuit s0 i i' -> Circuit s1 i' o -> Circuit (s0, s1) i o
iproj leak sim (s0, s1) i = do
  let (s0', i') = leak s0 i
  let (s1', o) = sim s1 i'
  ((s0', s1'), o)

-- TODO: I guess we don't really want the observation function to be a circuit
-- as well. We should change the projections in this file accordingly.
composeI
  :: Circuit s i o
  -> (o -> o')
  -> (s -> s')
  -> (s -> i -> (s', o'))
composeI impl obs proj = sproj proj $ oproj obs impl

-- composeI'
--   :: Circuit si i x
--   -> Circuit so x o
--   -> ((si, so) -> s')
--   -> ((si, so) -> i -> (s', o))
-- composeI' impl obs proj = sproj' proj $ iproj impl obs

composeS
  :: Circuit sl i x
  -> Circuit ss x o
  -> (s -> (sl, ss))
  -> (s -> i -> ((sl, ss), o))
composeS leak sim proj = sproj' proj $ iproj leak sim
