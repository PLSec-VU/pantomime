module Simplify
  ( simplifyExpr'
  , runSimplifier

  , noOpSimplifyExprOpts
  , noOpSimplMode
  ) where

import GHC.Plugins hiding (empty, (<>))

import GHC.Utils.Logger (getLogger)
import GHC.Unit.Env (ue_eps)

import GHC.Core.Opt.Simplify (SimplifyExprOpts (..), simplifyExpr)
import GHC.Core.Opt.Simplify.Env (SimplMode (..), FloatEnable (FloatDisabled))
import GHC.Core.Opt.Simplify.Monad
import GHC.Core.Unfold (UnfoldingOpts (..))
import GHC.Core.Opt.Arity (ArityOpts(..))
import GHC.Core.Rules.Config (RuleOpts(..))
import GHC.Core.Coercion.Opt (OptCoercionOpts(..))
import GHC.Platform (genericPlatform)

import GHC.MonadCore

import Control.Monad.Reader (ask)

import Types

-- | Simplifies an expression in the Core Monad.
--
-- Warning, even with all optimisations disabled via the SimplifyExprOpts, this
-- will still do a lot of transformations on the expression.
simplifyExpr' :: MonadCore m => SimplifyExprOpts -> Pass m CoreExpr
simplifyExpr' opts expr = liftCore $ do
  logger <- getLogger
  hscEnv <- getHscEnv
  let euc = ue_eps $ hsc_unit_env hscEnv
  liftIO $ simplifyExpr logger euc opts expr

-- | Run a simplifier in the Core Monad.
--
-- A more controlled way to use the GHC simplifier.
runSimplifier :: MonadCore m => MonadMod m => SimplM a -> m a
runSimplifier simpl = do
  dflags <- liftCore getDynFlags
  logger <- liftCore getLogger
  
  ruleEnv <- ask >>= liftCore . initRuleEnv
  let ruleEnv' = return ruleEnv
  let cfg = TopEnvConfig
        { te_history_size = historySize dflags
        , te_tick_factor = simplTickFactor dflags
        }
  let noInit = 0
  (x, _) <- liftCore . liftIO $ initSmpl logger ruleEnv' cfg noInit simpl
  return x

-- | Options for the expression simplifier with everything disabled.
noOpSimplifyExprOpts :: CompilerPhase -> String -> SimplifyExprOpts
noOpSimplifyExprOpts phase name = SimplifyExprOpts
  { se_fam_inst = []
  , se_mode = noOpSimplMode phase name
  , se_top_env_cfg = TopEnvConfig
    { te_history_size = 20
    , te_tick_factor = 100
    }
  }

-- | A simplifier mode with everything disabled.
noOpSimplMode :: CompilerPhase -> String -> SimplMode
noOpSimplMode phase name = SimplMode
  { sm_phase = phase
  , sm_names = [name]
  , sm_rules = False
  , sm_inline = False
  , sm_eta_expand = False
  , sm_cast_swizzle = False
  , sm_uf_opts = UnfoldingOpts
    { unfoldingCreationThreshold = 0
    , unfoldingUseThreshold = 0
    , unfoldingFunAppDiscount = 0
    , unfoldingDictDiscount = 0
    , unfoldingVeryAggressive = False
    , unfoldingCaseThreshold = 0
    , unfoldingCaseScaling = 0
    , unfoldingReportPrefix = Nothing
    }
  , sm_case_case = False
  , sm_pre_inline = False
  , sm_float_enable = FloatDisabled
  , sm_do_eta_reduction = False
  , sm_arity_opts = ArityOpts
    { ao_ped_bot = False
    , ao_dicts_cheap = False
    }
  , sm_rule_opts = RuleOpts
    { roPlatform = genericPlatform
    , roNumConstantFolding = False
    , roExcessRationalPrecision = False
    , roBignumRules = False
    }
  , sm_case_folding = False
  , sm_case_merge = False
  , sm_co_opt_opts = OptCoercionOpts False
  }


