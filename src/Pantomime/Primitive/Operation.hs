-- TODO: This should be renamed to Integer from operation.
-- TODO: Add top-level explanation of why we need this module and how it is
-- implemented under the hood. I guess with how we split off the primitives, it
-- would probably be good to have this explanation elsewhere though.
{-# LANGUAGE RoleAnnotations #-}

module Pantomime.Primitive.Operation
  ( Integer
  , plusInteger
  , timesInteger
  , absInteger
  , signumInteger
  , negateInteger
  , fromIntegerInteger
  ) where

import Prelude qualified as Prelude
import Prelude (Num (..), ($))

import Data.Coerce (coerce)

-- | Interpretable unbounded integer primitive.
--
-- Although this has an implementation for usage during runtime, it is expected
-- that this is primarily used to provide interpretations of other data types.
newtype Integer where
  Integer :: Prelude.Integer -> Integer

{-# OPAQUE plusInteger #-}
plusInteger :: Integer -> Integer -> Integer
plusInteger = coerce $ (+) @Prelude.Integer

{-# OPAQUE timesInteger #-}
timesInteger :: Integer -> Integer -> Integer
timesInteger = coerce $ (*) @Prelude.Integer

{-# OPAQUE absInteger #-}
absInteger :: Integer -> Integer
absInteger = coerce $ abs @Prelude.Integer

{-# OPAQUE signumInteger #-}
signumInteger :: Integer -> Integer
signumInteger = coerce $ signum @Prelude.Integer

{-# OPAQUE negateInteger #-}
negateInteger :: Integer -> Integer
negateInteger = coerce $ negate @Prelude.Integer

{-# OPAQUE fromIntegerInteger #-}
fromIntegerInteger :: Prelude.Integer -> Integer
fromIntegerInteger = coerce $ fromInteger @Prelude.Integer

instance Num Integer where
  (+) = plusInteger
  (*) = timesInteger
  abs = absInteger
  signum = signumInteger
  negate = negateInteger
  fromInteger = fromIntegerInteger
