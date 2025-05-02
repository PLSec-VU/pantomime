module Pantomime.Util
  ( foldM'
  , foldM_'
  , foldrM'
  , whyFail
  , maybeM
  , unwrap
  , (??=)

  , accumL
  , (%~~)

  , freshId
  , freshIds
  ) where

import GHC.Plugins hiding (empty)
import GHC.Core.Multiplicity (Scaled(..))

import Data.Foldable (foldrM)

import Control.Applicative
import Control.Monad (foldM, foldM_)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Trans.Maybe
import Control.Monad.State (state, runState)

import Lens.Micro (Lens)

-- | The usual 'foldM', but with its arguments switched.
--
-- The use for this is that one may use this to write an expression in the
-- following shape:
--
-- > res <- foldM' start xs $ \acc x -> do
-- >   ...
foldM' :: (Foldable t, Monad m) => b -> t a -> (b -> a -> m b) -> m b
foldM' acc xs f = foldM f acc xs

-- | The usual 'foldM_', but with its arguments switched.
--
-- The use for this is that one may use this to write an expression in the
-- following shape:
--
-- > foldM'_ start xs $ \acc x -> do
-- >   ...
foldM_' :: (Foldable t, Monad m) => b -> t a -> (b -> a -> m b) -> m ()
foldM_' acc xs f = foldM_ f acc xs

-- | The usual 'foldrM', but with its arguments switched.
--
-- The use for this is that one may use this to write an expression in the
-- following shape:
--
-- > res <- foldrM' start xs $ \x acc -> do
-- >   ...
foldrM' :: (Foldable t, Monad m) => b -> t a -> (a -> b -> m b) -> m b
foldrM' acc xs f = foldrM f acc xs

-- | Annotate why there was no result.
whyFail :: MonadError e m => e -> Maybe a -> m a
whyFail err = maybe (throwError err) pure

-- | Convert the given maybe into an alternative.
maybeM :: Alternative m => Maybe a -> m a
maybeM = maybe empty pure

-- | Unwrap the given monad, calling fail if the computation failed.
unwrap :: MonadFail m => MaybeT m a -> String -> m a
unwrap m str = runMaybeT m >>= \case
  Just a -> return a
  Nothing -> fail str

infixl 0 ??=

-- | An infix version of [`unwrap`].
(??=) :: MonadFail m => MaybeT m a -> String -> m a
(??=) = unwrap

-- | Accumulate a stateful function over a traversable input.
accumL :: Traversable f => (a -> s -> (b, s)) -> f a -> s -> (f b, s)
accumL f = runState . traverse (state . f)

infixr 4 %~~

-- | Update the outer record and get some inner value.
--
-- The inner value might be the adjusted value, but it could also be some
-- anything else produced by the modification function.
--
-- This function is intended to run some computation on an inner field, where
-- the computation additionally returns a value.
--
-- This is just an alias for lens application, but it can be confusing to apply
-- lenses directly. Especially since it would mean opaquely using a tuples as
-- the running monad. Additionally, this has a nicer precedence when applied in
-- the form:
-- ```
-- s & lens %~~ f
-- ```
(%~~) :: Lens s t a b -> (a -> (c, b)) -> s -> (c, t)
(%~~) = ($)


-- | Create a fresh variable.
--
-- Fetches a locally fresh unique from the in-scope set of the substitution.
-- Creates a new identifier and adds it to the in-scope set of the given
-- substitution.
freshId
  :: String
  -> Scaled Type
  -> InScopeSet
  -> (Id, InScopeSet)
freshId name (Scaled mult ty) scope = do
  -- Get a new unique value.
  let unique = unsafeGetFreshLocalUnique scope

  -- Create the fresh identifier.
  let name' = mkSystemName unique $ mkVarOcc name
  let identifier = mkLocalId name' mult ty

  -- Extend the scope and return it, together with the fresh identifier.
  let scope' = extendInScopeSet scope identifier
  (identifier, scope')

-- | Get multiple fresh identifiers via `freshId`.
freshIds
  :: Traversable f
  => f (String, Scaled Type)
  -> InScopeSet
  -> (f Id, InScopeSet)
freshIds = accumL $ uncurry freshId
