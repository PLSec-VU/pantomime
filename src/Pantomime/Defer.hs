{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Pantomime.Defer
  -- | The main function of this module.
  --
  -- This allows effectful computation to be escaped as long as it eventually
  -- is enclosed again, deferring the trigger of any effects until the value
  -- is forced.
  ( Deferrable
  , DeferWith
  , Defer (..) -- TODO: Remove this export once we rid of 'Eval'.
  , defer
  , withDeferrable
  ) where

import Control.DeepSeq (NFData)
import Data.Composition ((.:))
import Data.Constraint (Dict(..))
import Data.Constraint.Unsafe (unsafeAxiom)
import Data.Kind (Constraint)
import Effectful (Eff, Effect)
import Effectful.Context (Context, ContextMode (..))
import Effectful.Dispatch.Static (unsafeEff, unEff)
import Effectful.Dispatch.Static.Primitive (Env)
import Effectful.Error.Static (Error)
import Effectful.Exception (evaluateDeep)
import Effectful.Reader.Static (Reader)
import GHC.IO (unsafeDupablePerformIO)

-- | Whether all effects in the stack can be deferred.
type family DeferWith (es :: [Effect]) :: Constraint where
  DeferWith '[] = ()
  DeferWith (Error err : es) = DeferWith es
  DeferWith (Reader env : es) = DeferWith es
  DeferWith (Context 'Reader env : es) = DeferWith es

-- | Helper class to 'defer' both values and functions.
class Deferrable es => Defer es a | a -> es where
  -- | The value that is the result of deferring the effect.
  type Deferred a

  -- | Helper instance to be used in the final 'defer'.
  defer'
    :: a
    -> Env es
    -> Deferred a

instance Deferrable es => Defer es (Eff es a) where
  type Deferred (Eff es a) = a

  defer' = unsafeDupablePerformIO .: unEff

instance Defer es b => Defer es (a -> b) where
  type Deferred (a -> b) = (a -> Deferred b)

  defer' f env x = defer' (f x) env

-- | Defer an effectful computation.
--
-- The intent is that a user can capture all effects inside of the pure value as
-- a thunk, as long as the computation stays inside of an 'Eff' at an outer
-- layer.
defer :: Defer es a => a -> Eff es (Deferred a)
defer x = unsafeEff $ pure . defer' x

-- | Typeclass to ensure no instance can be made of a typeclass outside of this
-- module.
class Private

-- | Whether we actively allow for deferring the computation.
--
-- This constraint should only be obtained via 'withDeferrable'.
class Private => Deferrable (es :: [Effect])

-- | Get the typeclass constraint that allows us to call 'defer'.
--
-- Note the 'NFData' constraint to ensure any deferred instances of 'Error' do
-- not leave their scope.
withDeferrable
  :: forall es a
   . DeferWith es
  => NFData a
  => (Deferrable es => Eff es a)
  -> Eff es a
withDeferrable action = do
  -- NOTE: We force usage to remove the unused constraint warning.
  let _ = Dict @(DeferWith es)
  Dict <- pure $ unsafeAxiom @(Deferrable es)
  result <- action
  evaluateDeep result
