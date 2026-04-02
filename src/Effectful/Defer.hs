{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Effectful.Defer
  -- | The main function of this module.
  --
  -- This allows effectful computation to be escaped as long as it eventually
  -- is enclosed again, deferring the trigger of any effects until the value
  -- is forced.
  ( Deferrable
  , defer

  -- | An error type that supports 'Deferrable'.
  , Error
  , runError
  , runErrorWith
  , runErrorNoCallStack
  , throwErrorWith
  , throwError
  , throwError_
  , catchError
  , handleError
  , tryError
  ) where

import Control.DeepSeq (NFData)
import Data.Coerce (coerce)
import Data.Composition ((.:))
import Data.Kind (Type, Constraint)
import Effectful (Eff, Effect, DispatchOf, Dispatch (..), type (:>))
import Effectful.Dispatch.Static
  ( StaticRep
  , SideEffects (..)
  , unsafeEff_
  , evalStaticRep, getStaticRep, unsafeEff, unEff
  )
import Effectful.Exception
  ( Exception (..)
  , tryJust
  , evaluateDeep
  , asyncExceptionToException
  , asyncExceptionFromException, throwIO, catchJust
  )
import Effectful.Internal.Env (Env)
import Effectful.Internal.Utils (Unique, Any, newUnique, fromAny, toAny)
import Effectful.Reader.Static (Reader)
import GHC.IO.Unsafe (unsafeDupablePerformIO)
import GHC.Stack
  ( HasCallStack
  , CallStack
  , prettyCallStack
  , withFrozenCallStack
  , callStack
  )

-- | Whether all effects in the stack can be deferred.
type family Deferrable (es :: [Effect]) :: Constraint

type instance Deferrable '[] = ()
type instance Deferrable (Error err : es) = Deferrable es
type instance Deferrable (Reader env : es) = Deferrable es

-- | Helper class to 'defer' both values and functions.
class Deferrable es => Defer es a | a -> es where
  -- | The value that is the result of deferring the effect.
  type Deferred a

  -- | Helper instance to be used in the final 'defer'.
  defer'
    :: Deferrable es
    => a
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
--
-- One useful instance is the 'Error' type defined in this class. One can
defer :: Defer es a => a -> Eff es (Deferred a)
defer x = unsafeEff $ pure . defer' x

-- | Provide the ability to handle errors of type @e@.
--
-- Note that this error is slightly different from the regular error in that its
-- effect can be deferred into a thunk via 'defer'. To allow for this, the
-- handler needs to normalise the inner value via 'NFData' to ensure no thunk
-- escapes with an error thrown through this effect handler.
data Error (e :: Type) :: Effect

type instance DispatchOf (Error e) = Static NoSideEffects
newtype instance StaticRep (Error e) = Error ErrorId

-- | Handle errors of type @e@.
--
-- Note that in contrast with standard effectful error, this version requires
-- the result to be put in normal form. This is a hard requirement to ensure
-- no error thunk escapes the effect handler. Otherwise, we violate the
-- requirement that this effect is 'Deferrable'.
runError
  :: forall e es a
   . HasCallStack
  => NFData a
  => Eff (Error e : es) a
  -> Eff es (Either (CallStack, e) a)
runError action = do
  eid <- unsafeEff_ newErrorId
  evalStaticRep (Error @e eid) do
    tryJust (matchError eid) $ action >>= evaluateDeep

-- | Handle errors of type @e@ with a specific error handler.
runErrorWith
  :: HasCallStack
  => NFData a
  => (CallStack -> e -> Eff es a)
  -- ^ The error handler.
  -> Eff (Error e : es) a
  -> Eff es a
runErrorWith handler action = runError action >>= \case
  Left (cs, e) -> handler cs e
  Right a -> pure a

-- | Handle errors of type @e@. In case of an error discard the 'CallStack'.
runErrorNoCallStack
  :: forall e es a
   . HasCallStack
  => NFData a
  => Eff (Error e : es) a
  -> Eff es (Either e a)
runErrorNoCallStack = fmap (either (Left . snd) Right) . runError

-- | Throw an error of type @e@ and specify a display function in case a
-- third-party code catches the internal exception and 'show's it.
throwErrorWith
  :: forall e es a. (HasCallStack, Error e :> es)
  => (e -> String)
  -- ^ The display function.
  -> e
  -- ^ The error.
  -> Eff es a
throwErrorWith display e = do
  Error eid <- getStaticRep @(Error e)
  withFrozenCallStack throwIO $ ErrorWrapper eid callStack (display e) (toAny e)

-- | Throw an error of type @e@ with 'show' as a display function.
throwError
  :: forall e es a. (HasCallStack, Error e :> es, Show e)
  => e
  -- ^ The error.
  -> Eff es a
throwError = withFrozenCallStack throwErrorWith show

-- | Throw an error of type @e@ with no display function.
throwError_
  :: forall e es a. (HasCallStack, Error e :> es)
  => e
  -- ^ The error.
  -> Eff es a
throwError_ = withFrozenCallStack throwErrorWith (const "<opaque>")

-- | Handle an error of type @e@.
catchError
  :: forall e es a. (HasCallStack, Error e :> es)
  => Eff es a
  -- ^ The inner computation.
  -> (CallStack -> e -> Eff es a)
  -- ^ A handler for errors in the inner computation.
  -> Eff es a
catchError action handler = do
  Error eid <- getStaticRep @(Error e)
  catchJust (matchError eid) action $ uncurry handler

-- | The same as @'flip' 'catchError'@, which is useful in situations where the
-- code for the handler is shorter.
handleError
  :: forall e es a. (HasCallStack, Error e :> es)
  => (CallStack -> e -> Eff es a)
  -- ^ A handler for errors in the inner computation.
  -> Eff es a
  -- ^ The inner computation.
  -> Eff es a
handleError = flip catchError

-- | Similar to 'catchError', but returns an 'Either' result which is a 'Right'
-- if no error was thrown and a 'Left' otherwise.
tryError
  :: forall e es a. (HasCallStack, Error e :> es)
  => Eff es a
  -- ^ The inner computation.
  -> Eff es (Either (CallStack, e) a)
tryError action = do
  Error eid <- getStaticRep @(Error e)
  tryJust (matchError eid) action

newtype ErrorId = ErrorId Unique
  deriving Eq

-- | A unique is picked so that distinct 'Error' handlers for the same type
-- don't catch each other's exceptions.
newErrorId :: IO ErrorId
newErrorId = coerce newUnique

data ErrorWrapper = ErrorWrapper !ErrorId CallStack String Any

instance Show ErrorWrapper where
  showsPrec _ (ErrorWrapper _ cs errRep _)
    = ("Effectful.Error.Static.ErrorWrapper: " ++)
    . (errRep ++)
    . ("\n" ++)
    . (prettyCallStack cs ++)

instance Exception ErrorWrapper where
  -- See discussion in https://github.com/haskell-effectful/effectful/pull/232.
  toException = asyncExceptionToException
  fromException = asyncExceptionFromException

matchError :: ErrorId -> ErrorWrapper -> Maybe (CallStack, e)
matchError eid (ErrorWrapper etag cs _ e)
  | eid == etag = Just (cs, fromAny e)
  | otherwise = Nothing
