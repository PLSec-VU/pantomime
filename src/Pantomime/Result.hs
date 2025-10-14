{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}

module Pantomime.Result
  ( Error
  , type (!>)
  , weaken
  , raise
  , embed
  , absurd
  , location

  , Result
  , ok
  , throw
  , handle
  , failWith
  ) where

import Data.Kind (Type)

import GHC.TypeLits (TypeError, ErrorMessage (..))
import GHC.Types (Any)
import GHC.Stack (CallStack, HasCallStack, callStack, withFrozenCallStack)

import Unsafe.Coerce (unsafeCoerce)

-- | An error value that inhabits one of the types in @es@.
data Error (es :: [Type]) where
  Error :: !Int -> CallStack -> Any -> Error es

-- | A constraint that requires a particular error @e@ to be a member of the
-- type-level list @es@. This is used to parameterize an 'Error' computation
-- over an arbitrary list of effects, so long as @e@ is /somewhere/ in the list.
class e !> (es :: [Type]) where
  reifyIndex :: Int

instance TypeError
  ( Text "There is no handler for '" :<>: ShowType e :<>: Text "' in the context"
  ) => e !> '[] where
  reifyIndex = error "unreachable"

instance {-# OVERLAPPING #-} e !> (e : es) where
  reifyIndex = 0

instance e !> es => e !> (f : es) where
  reifyIndex = 1 + reifyIndex @e @es

-- | Weaken an error value by handling one of its cases.
weaken
  :: forall e es
   . Error (e : es)
  -> Either (CallStack, e) (Error es)
weaken (Error idx cs err) = case idx of
  0 -> Left $ (cs, unsafeCoerce @_ @e err)
  _ -> Right $ Error (idx - 1) cs err

-- | Raise an error value to encompass more errors.
raise
  :: forall e es
   . Error es
  -> Error (e : es)
raise (Error idx cs err) = Error (idx + 1) cs err

-- | Embed a value into an 'Error'.
embed
  :: forall e es
   . HasCallStack
  => e !> es
  => e
  -> Error es
embed = Error (reifyIndex @e @es) callStack . unsafeCoerce

-- | There are no inhabitants for this error type.
absurd :: Error '[] -> a
absurd !_ = error "unreachable"

-- | Gather the location where the error happened.
location :: Error es -> CallStack
location (Error _ cs _) = cs

-- | Synonym for using 'Error' within a monadic context.
type Result es a = Either (Error es) a

-- | Given that the error in the result is vacuous, we can simply unwrap the
-- result.
ok :: Result '[] a -> a
ok = either absurd id

-- | Throw an error within the context of the result.
throw
  :: HasCallStack
  => e !> es
  => e
  -> Result es a
throw = Left . withFrozenCallStack embed

-- | Handle the top error in the result.
handle
  :: forall e a es
   . Result (e : es) a
  -> Either (CallStack, e) (Result es a)
handle = \case
  Right value -> Right $ Right value
  Left err -> Left <$> weaken err

-- | Convert a 'Maybe' value into a 'Result', with the given error for the
-- 'Nothing' case.
failWith
  :: HasCallStack
  => e !> es
  => e
  -> Maybe a
  -> Result es a
failWith err = maybe (withFrozenCallStack throw err) pure
