{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Pantomime.Primitive.Bool
  ( Bool (True, False)
  , true
  , false
  , ite
  , concrete
  ) where

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

-- | Convert a symbolic Boolean to the standard Haskell Boolean.
concrete :: Bool -> Prelude.Bool
concrete value = ite value Prelude.True Prelude.False

pattern True :: Bool
pattern True <- (concrete -> Prelude.True)
  where
    True = true

pattern False :: Bool
pattern False <- (concrete -> Prelude.False)
  where
    False = false

{-# COMPLETE True, False #-}
