{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Pantomime.Primitive.Bool
  ( Bool (True, False)
  , true
  , false
  , ite
  , concrete
  , not
  , (&&)
  , (||)
  , xor
  , iff
  ) where

import Data.Composition ((.:))
import Prelude qualified

-- TODO: We should provide implementations for many of the common typeclasses.
-- For now, this suffices.
-- TODO: Another thing to look into is conversion between primitive types. Idk
-- if there for example is a primitive operation to convert between an boolean
-- and a single-bit bitvector.
-- | Pantomime primitive Boolean.
newtype Bool where
  Bool :: Prelude.Bool -> Bool

{-# OPAQUE true #-}
true :: Bool
true = Bool Prelude.True

{-# OPAQUE false #-}
false :: Bool
false = Bool Prelude.False

-- TODO: I guess we should be runtime polymorphic on the value (like a real
-- Haskell if-then-else).
{-# OPAQUE ite #-}
ite :: Bool -> a -> a -> a
ite (Bool scrut) tr fl = case scrut of
  Prelude.True -> tr
  Prelude.False -> fl

-- WARNING: Helper functions should only interact with 'Bool' via the primitive
-- functions that are marked as 'OPAQUE'. These primitive functions are
-- interpreted in the backend of symbolic executor. Any direct unwrapping of
-- 'Bool' will crash the execution if it is reached.
--
-- Many of the helper functions will look verbose and are written in a somewhat
-- roundabout way. This is intentional, do not change them unless you know what
-- you're doing!

pattern True :: Bool
pattern True <- (concrete -> Prelude.True)
  where
    True = true

pattern False :: Bool
pattern False <- (concrete -> Prelude.False)
  where
    False = false

{-# COMPLETE True, False #-}

-- | Convert a symbolic Boolean to the standard Haskell Boolean.
concrete :: Bool -> Prelude.Bool
concrete value = ite value Prelude.True Prelude.False

-- TODO: Although I now implemented these operations through only ite, it is
-- likely better to use OPAQUE interpretations for these as well. Especially for
-- xor and ite, Grisette is not able to optimise the current definition into
-- their succinct form.
not :: Bool -> Bool
not = \case
  True -> False
  False -> True

(&&) :: Bool -> Bool -> Bool
(&&) = \cases
  True y -> y
  False _ -> False

(||) :: Bool -> Bool -> Bool
(||) = \cases
  True _ -> True
  False y -> y

xor :: Bool -> Bool -> Bool
xor = \cases
  True False -> True
  False True -> True
  _ _ -> False

iff :: Bool -> Bool -> Bool
iff = \cases
  True True -> True
  False False -> True
  _ _ -> False

instance Prelude.Eq Bool where
  (==) = concrete .: iff
