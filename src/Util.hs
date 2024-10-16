module Util
  ( bindPass
  , fix
  , fuse
  , (<|-|>)

  , maybeM
  , unwrap
  , (??=)

  , freshTyVar
  , freshLocalVar
  , freshGlobalVar

  , resolveTH
  , resolveTH'
  , lookupLocal
  , thNameToGhcName'
  , getInstEnvs'

  , lintExpr'
  , resolveInstance
  ) where

import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad ((>=>))
import Control.Monad.Reader (reader)

import GHC.MonadCore
import GHC.Plugins hiding (empty, (<>))
import GHC.Types.TyThing (lookupId)
import GHC.Core.InstEnv (InstEnvs (..), lookupUniqueInstEnv, instanceDFunId)
import GHC.Unit.External (eps_inst_env)
import GHC.Data.Maybe (rightToMaybe)
import GHC.Data.Bag (Bag)

import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.Core.Lint

import Data.Maybe (mapMaybe, listToMaybe)
import Data.List (foldl')

import Data.Data
import Data.Generics hiding (empty)

import qualified Language.Haskell.TH.Syntax as TH

import Types

-- | Maps an expression pass over a binder.
bindPass :: MonadCore m => Pass m (Expr a) -> Pass m (Bind' a)
bindPass f (Bind' x e) = Bind' x <$> f e

-- | Run the given pass until a fixed point is reached. That is, the given pass
-- does not produce a new result.
fix :: MonadCore m => Data a => Pass (MaybeT m) a -> Pass m a
fix f = everywhereM $ mkM go
  where
    go e = runMaybeT (f e) >>= \case
      Just e' -> fix f e'
      Nothing -> return e

-- | Fuse all the given passes; the first succesful pass wil return its result.
fuse :: Alternative m => [Pass m a] -> Pass m a
fuse = foldl' (<|-|>) $ const empty

-- | Fuses two passes; the first succesful pass will return its result.
(<|-|>) :: Alternative m => Pass m a -> Pass m a -> Pass m a
(<|-|>) p p' e = p e <|> p' e

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

freshTyVar :: MonadCore m => String -> Kind -> m Var
freshTyVar name kind = do
  unique <- liftCore getUniqueM
  let name' = mkSystemName unique $ mkVarOcc name
  let var = mkTyVar name' kind
  return var

-- | Creates a fresh variable.
freshLocalVar :: MonadCore m => String -> Type -> m Var
freshLocalVar name ty = do
  unique <- liftCore getUniqueM
  let name' = mkSystemName unique $ mkVarOcc name
  let var = mkLocalVar VanillaId name' ManyTy ty vanillaIdInfo
  return var

-- | Creates a fresh variable.
freshGlobalVar :: MonadCore m => String -> Type -> m Var
freshGlobalVar name ty = do
  unique <- liftCore getUniqueM
  let name' = mkSystemName unique $ mkVarOcc name
  let var = mkGlobalVar VanillaId name' ty vanillaIdInfo
  return var

-- | Resolves a template haskell name to a non-recursive variable.
resolveTH :: Alternative m => MonadCore m => MonadMod m => TH.Name -> m Var
resolveTH thName = do
  name <- thNameToGhcName' thName 
  let lookupLocal' = do
        Bind' x _ <- lookupLocal $ \v -> varName v == name
        pure x
  let lookupId' = liftCore $ lookupId name
  lookupLocal' <|> lookupId'

-- | Same as `lookupTH`, but emits an error on failure.
resolveTH' :: MonadFail m => MonadCore m => MonadMod m => TH.Name -> m Var
resolveTH' name = resolveTH name
  ??= "Could not resolve function: " <> TH.nameBase name

-- | Lookup a local non-recursive binder.
lookupLocal :: Alternative m => MonadMod m => (Var -> Bool) -> m CoreBind'
lookupLocal cmp = do
  prog <- reader mg_binds
  let firstJust f = maybeM . listToMaybe . mapMaybe f
  let cmp' = \case
        NonRec x e | cmp x -> Just $ Bind' x e
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
getInstEnvs' :: MonadCore m => MonadMod m => m InstEnvs
getInstEnvs' = do
  -- Get the global definitions
  hscEnv <- liftCore getHscEnv
  eps <- liftCore . liftIO $ hscEPS hscEnv
  let global = eps_inst_env eps

  -- Get the local definitions
  local <- reader mg_inst_env

  -- Return the instance environments
  return $ InstEnvs
    { ie_global = global
    , ie_local = local
    -- TODO: Get actual visible orphan modules
    , ie_visible = mkModuleSet []
    }

-- | Fetch a dictionary identifier.
--
-- Lookup an instance of the predicate type. We return the dictionary variable
-- that corresponds to the instance.
resolveInstance :: Alternative m => MonadCore m => MonadMod m => PredType -> m DFunId
resolveInstance predTy = do
  instEnvs <- getInstEnvs'
  (tyCon, tyArgs) <- maybeM $ splitTyConApp_maybe predTy
  tyClass <- maybeM $ tyConClass_maybe tyCon
  let eitherInst = lookupUniqueInstEnv instEnvs tyClass tyArgs
  (clsInst, _) <- maybeM $ rightToMaybe eitherInst
  let dictVar = instanceDFunId clsInst
  return dictVar

lintExpr' :: MonadCore m => CoreExpr -> m (Maybe (Bag SDoc))
lintExpr' expr = do
  dflags <- liftCore getDynFlags
  let vars = exprFreeVarsList expr
  let cfg = initLintConfig dflags vars
  return $ lintExpr cfg expr
