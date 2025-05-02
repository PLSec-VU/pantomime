module Pantomime.Combinator
  ( Circuit
  , oproj
  , sproj
  , sproj'
  , iproj
  , compose
  , composeI
  , composeS
  ) where

type Circuit s i o = (s -> i -> (s, o))

oproj :: (o -> o') -> Circuit s i o -> Circuit s i o'
oproj obs impl s i = do
  let (s', o) = impl s i
  (s', obs o)

sproj :: (s -> s') -> Circuit s i o -> (s -> i -> (s', o))
sproj proj circuit s i = do
  let (s', o) = circuit s i
  (proj s', o)

sproj' :: (s -> s') -> Circuit s' i o -> (s -> i -> (s', o))
sproj' proj circuit s = circuit (proj s)

iproj :: Circuit s0 i i' -> Circuit s1 i' o -> Circuit (s0, s1) i o
iproj = compose

-- | Sequential composition of two circuits.
compose
  :: Circuit s0 i a
  -> Circuit s1 a o
  -> Circuit (s0, s1) i o
compose c0 c1 (s0, s1) i = do
  let (s0', x) = c0 s0 i
  let (s1', o) = c1 s1 x
  ((s0', s1'), o)

-- | Construct the implementation part of the proof.
composeI
  :: Circuit si i o
  -> Circuit so o o'
  -> ((si, so) -> s)
  -> ((si, so) -> i -> (s, o'))
composeI impl obs proj = sproj proj $ compose impl obs

-- | Construct the simulator part of the proof.
composeS
  :: Circuit sl i x
  -> Circuit ss x o
  -> (s -> (sl, ss))
  -> (s -> i -> ((sl, ss), o))
composeS leak sim proj = sproj' proj $ compose leak sim
