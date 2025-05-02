module Util
  ( maybeM
  , unwrap
  , (??=)

  , fuse
  , (<|-|>)

  , accumL
  , (%~~)
  , freshId
  , freshIds
  , freshLocalVar
  , freshGlobalVar
  , zapOccInfo

  , resolveTH
  , resolveTH'
  , lookupLocal
  , thNameToGhcName'
  , getInstEnvs'
  , getFamInstEnvs'
  ) where

import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad ((>=>))
import Control.Monad.State (state, runState)

import GHC.Plugins hiding (empty, (<>))
import GHC.MonadCore
import GHC.Types.TyThing (lookupId)
import GHC.Core.InstEnv (InstEnvs (..))
import GHC.Core.TyCo.Rep (Scaled (..))
import GHC.Core.FamInstEnv (FamInstEnvs)
import GHC.Unit.External (eps_inst_env)

import qualified Language.Haskell.TH.Syntax as TH

import Data.Maybe (mapMaybe, listToMaybe)
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import Lens.Micro (Lens)

import Pantomime.Monad.GHC

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

-- | Fuse all the given passes; the first succesful pass wil return its result.
fuse :: Alternative m => [a -> m b] -> a -> m b
fuse = foldl' (<|-|>) $ const empty

-- | Fuses two passes; the first succesful pass will return its result.
(<|-|>) :: Alternative m => (a -> m b) -> (a -> m b) -> (a -> m b)
(<|-|>) p p' e = p e <|> p' e

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
-- Created the new identifier as per the arguments and adds it to the in-scope
-- set of the given substitution. In this way, one can create a new fresh id
-- with this updated substitution.
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

-- TODO: I think we don't use this anymore. We should prune it!
-- | Creates a fresh variable.
freshLocalVar :: MonadCore m => String -> Mult -> Type -> m Var
freshLocalVar name mult ty = do
  unique <- liftCore getUniqueM
  let name' = mkSystemName unique $ mkVarOcc name
  let var = mkLocalVar VanillaId name' mult ty vanillaIdInfo
  return var

-- TODO: I think we don't use this anymore. We should prune it!
-- | Creates a fresh variable.
freshGlobalVar :: MonadCore m => String -> Type -> m Var
freshGlobalVar name ty = do
  unique <- liftCore getUniqueM
  let name' = mkSystemName unique $ mkVarOcc name
  let var = mkGlobalVar VanillaId name' ty vanillaIdInfo
  return var

-- | Zap occurance information of an expression.
--
-- The main purpose for this function is to inspect variable shadowing of a term
-- within the context of dead variables, which are not printed otherwise.
zapOccInfo :: CoreExpr -> CoreExpr
zapOccInfo = everywhere $ mkT zap
  where
    zap var
      | isId var = zapIdOccInfo var
      | otherwise = var

-- | Resolves a template haskell name to a non-recursive variable.
resolveTH
  :: Alternative m
  => MonadCore m
  => HasModGuts' m
  => TH.Name
  -> m Var
resolveTH thName = do
  name <- thNameToGhcName' thName
  asum [lookupLocal name, liftCore $ lookupId name]

-- | Same as `lookupTH`, but emits an error on failure.
resolveTH'
  :: MonadFail m
  => MonadCore m
  => HasModGuts' m
  => TH.Name
  -> m Var
resolveTH' name = resolveTH name
  ??= "Could not resolve expression: " <> TH.nameBase name

-- | Lookup a local non-recursive variable.
lookupLocal
  :: Alternative m
  => HasModGuts' m
  => Name
  -> m Var
lookupLocal name = do
  prog <- mg_binds <$> modGuts'
  let firstJust f = maybeM . listToMaybe . mapMaybe f
  let cmp' = \case
        NonRec x _ | name == varName x -> Just x
        _ -> Nothing
  firstJust cmp' prog

-- | Attempts to convert a template haskell name into a Core name. Wrapper of
-- `thNameToGhcName`, but made polymorphic on the monad.
thNameToGhcName' :: Alternative m => MonadCore m => TH.Name -> m Name
thNameToGhcName' = liftCore . thNameToGhcName >=> maybeM

-- | Fetch the instance environments.
--
-- Get the instance environments from a CoreM pass instead of the typechecker
-- pass.
getInstEnvs'
  :: MonadCore m
  => HasModGuts' m
  => m InstEnvs
getInstEnvs' = do
  -- Get the global definitions
  hscEnv <- liftCore getHscEnv
  eps <- liftCore . liftIO $ hscEPS hscEnv
  let global = eps_inst_env eps

  -- Get the local definitions
  local <- mg_inst_env <$> modGuts'

  -- Return the instance environments
  return $ InstEnvs
    { ie_global = global
    , ie_local = local
    -- TODO: Get actual visible orphan modules
    , ie_visible = mkModuleSet []
    }

getFamInstEnvs'
  :: MonadCore m
  => HasModGuts' m
  => m FamInstEnvs
getFamInstEnvs' = do
  local <- mg_fam_inst_env <$> modGuts'
  global <- liftCore getPackageFamInstEnv
  pure (local, global)
