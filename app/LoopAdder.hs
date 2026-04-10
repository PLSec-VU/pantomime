{-# OPTIONS_GHC -w #-}

module LoopAdder (test1) where

import Prelude hiding (seq,id,init)

import Data.Maybe (fromMaybe)

type Circ s i o = s -> i -> (s, o)

{------------------------------ Adder ------------------------------}
-- fast path in both inputs
add :: Circ (Maybe Int) (Maybe Int, Maybe Int) (Maybe Int)
add (Just res) _       = (Nothing, Just res) 
add _ (Just 0, Just b) = (Nothing, Just b)
add _ (Just a, Just 0) = (Nothing, Just a)
add _ (Just a, Just b) = (Just $ a+b, Nothing)
add _ _                = (Nothing, Nothing)

{------------------------------ Circuit Combinators ------------------------------}

-- compose two circuits sequentially
seq :: (Circ s1 i io) -> (Circ s2 io o) -> (Circ (s1,s2) i o)
seq c1 c2 (s1, s2) i  = ((s1', s2'), o)
  where
    (s1', io) = c1  s1 i
    (s2', o)  = c2  s2 io

-- compose two circuits parallely
par :: (Circ s1 i1 o1) -> (Circ s2 i2 o2) -> (Circ (s1,s2) (i1,i2) (o1,o2))
par c1 c2 (s1, s2) (i1,i2)  = ((s1', s2'), (o1, o2))
  where
    (s1', o1) = c1  s1 i1
    (s2', o2)  = c2  s2 i2

loopy :: Circ s (r,i) (r,o) -> Circ (s,r) i o
loopy c (s,r) i = ((s',r'), o)
    where
      (s', (r',o)) = c s (r,i)

lift :: (i->o) -> Circ () i o
lift f _ i  = ((), f i)

{------------------------- Basic circuits ----------------------------}

-- identity circuit
id :: Circ () a a 
id _ a = ((), a)

-- left duplication
dupL :: Circ () (a,b) (a,(a,b))
dupL _ (a,b) = ((),(a,(a,b)))

-- right duplication
dupR :: Circ () (a,b) ((a,b),b)
dupR _ (a,b) = ((),((a,b),b))

-- Helpers
just :: a -> Maybe a
just a = Just a

comb :: (a, Maybe a) -> a
comb (a, b) = fromMaybe a b

{--------------------------- Combined Circuit ----------------------------}
-- | Gets a Maybe Int input, adds it to the internal register, and       --
-- | outputs the sum. The internal adder takes 2 cycles but has fast     --
-- | paths on 0.                                                         --
{-------------------------------------------------------------------------}

addSt = loopy (pre `seq` (id `par` add) `seq` post)
pre = dupL `seq` (id `par` ((lift just) `par` id))
post = dupR `seq` (lift comb `par` id)


{------------------------------ Testing ------------------------------}
mealy :: (Circ s i o) -> s -> [i] -> [o]
mealy _ s [] = []
mealy c s (i:is) = o:os
  where 
    os = mealy c s' is
    (s', o) = c s i
init = (((((), ((), ((), ()))), ((), Nothing)), ((), ((), ()))), 0)
run is = mealy addSt init is

test1 = run [Just 1, Just 1, Nothing, Just 0, Just 1, Nothing]