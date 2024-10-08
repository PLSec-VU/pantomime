module Util
  ( maybeM
  , unwrap
  , (??=)

  , fix
  , fuse
  , (<|-|>)

  , freshTyVar
  , freshLocalVar
  , freshGlobalVar

  , resolveTH
  , resolveTH'
  , lookupLocal
  , thNameToGhcName'
  , getInstEnvs'

  , simplifyExpr'
  , noOpSimplifyExprOpts

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
import GHC.Utils.Logger (getLogger)
import GHC.Unit.Env (ue_eps)

import GHC.Core.Opt.Simplify (SimplifyExprOpts (..), simplifyExpr)
import GHC.Core.Opt.Simplify.Env (SimplMode (..), FloatEnable (FloatDisabled))
import GHC.Core.Opt.Simplify.Monad
import GHC.Core.Unfold (defaultUnfoldingOpts)
import GHC.Core.Opt.Arity (ArityOpts(..))
import GHC.Core.Rules.Config (RuleOpts(..))
import GHC.Core.Coercion.Opt (OptCoercionOpts(..))

import Data.Maybe (mapMaybe, listToMaybe)
import Data.List (foldl')

import Data.Data
import Generics.SYB hiding (empty)

import qualified Language.Haskell.TH.Syntax as TH

import Types

-- | Run the given pass until a fixed point is reached. That is, the given pass
-- does not produce a new result.
fix :: (MonadCore m, Data a) => Pass (MaybeT m) a -> Pass m a
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
  -- test <- reader mg_binds
  -- dbg test

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

-- | Simplifies an expression in the Core Monad.
simplifyExpr' :: MonadCore m => SimplifyExprOpts -> Pass m CoreExpr
simplifyExpr' opts expr = liftCore $ do
  logger <- getLogger
  hscEnv <- getHscEnv
  let euc = ue_eps $ hsc_unit_env hscEnv
  liftIO $ simplifyExpr logger euc opts expr

noOpSimplifyExprOpts :: MonadCore m => CompilerPhase -> [String] -> m SimplifyExprOpts
noOpSimplifyExprOpts phase names = do
  dflags <- liftCore getDynFlags
  return SimplifyExprOpts
    { se_fam_inst = []
    , se_mode = SimplMode
      { sm_phase = phase
      , sm_names = names
      , sm_rules = False
      , sm_inline = False
      , sm_eta_expand = False
      , sm_cast_swizzle = False
      , sm_uf_opts = defaultUnfoldingOpts
      , sm_case_case = False
      , sm_pre_inline = False
      , sm_float_enable = FloatDisabled
      , sm_do_eta_reduction = False
      , sm_arity_opts = ArityOpts
        { ao_ped_bot = False
        , ao_dicts_cheap = False
        }
      , sm_rule_opts = RuleOpts
        { roPlatform = targetPlatform dflags
        , roNumConstantFolding = False
        , roExcessRationalPrecision = False
        , roBignumRules = False
        }
      , sm_case_folding = False
      , sm_case_merge = False
      , sm_co_opt_opts = OptCoercionOpts False
      }
    , se_top_env_cfg = TopEnvConfig
      { te_history_size = 20
      , te_tick_factor = 100
      }
    }
