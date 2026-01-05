{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Pantomime.Primitive.Bool
  ( Bool (True, False)
  , true
  , false
  , ite
  ) where

import Prelude qualified as Prelude

-- TODO: We should provide implementations for many of the common typeclasses.
-- For now, this suffices.
-- TODO: Another thing to look into is conversion between primitive types. Idk
-- if there for example is a primitive operation to convert between an boolean
-- and a single-bit bitvector.
-- | Pantomime primitive Boolean.
data Bool where
  -- See note on pattern synonyms for 'True' and 'False' why we define it as
  -- such.
  True' :: Bool
  False' :: Bool

{-# OPAQUE true #-}
true :: Bool
true = True'

{-# OPAQUE false #-}
false :: Bool
false = False'

{-# OPAQUE ite #-}
ite :: Bool -> a -> a -> a
ite scrut tr fl = case scrut of
  True' -> tr
  False' -> fl

-- | Convert a symbolic Boolean to the standard Haskell Boolean.
concrete :: Bool -> Prelude.Bool
concrete value = ite value Prelude.True Prelude.False

-- NOTE: To correctly link the Boolean defined in this module with the symbolic
-- Boolean primitive of Pantomime, we should never use the data constructors
-- 'True'' and 'False'' outside of 'OPAQUE' functions. That is, there is no good
-- way to interpret a pattern match.
--
-- As such, we can only expose a pattern match on 'Bool' via a pattern synonym
-- that implements both directions via 'OPAQUE' functions.
pattern True :: Bool
pattern True <- (concrete -> Prelude.True)
  where
    True = true

pattern False :: Bool
pattern False <- (concrete -> Prelude.False)
  where
    False = false

{-# COMPLETE True, False #-}
