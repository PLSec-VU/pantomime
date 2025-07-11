-- TODO: There are quite a few more effects we should write for the external
-- package registry. For now, we will extend it on a by need basis.
-- TODO: Module level comments.

module Effectful.GHC.External
  ( HasExternalPackageState (..)
  , getExternalPackageState

  , HasInstEnvs (..)
  , getInstEnvs
  , runHasInstEnvs
  , runHasInstEnvs'

  , HasFamInstEnvs (..)
  , getFamInstEnvs
  , runHasFamInstEnv
  ) where

import Effectful
import Effectful.Dispatch.Dynamic (send, interpret_)

import GHC.Plugins
import GHC.Core.FamInstEnv (FamInstEnv, FamInstEnvs)
import GHC.Core.InstEnv (InstEnv, InstEnvs (..))
import GHC.Unit.External (ExternalPackageState (..))
import GHC.Unit.Module.Deps (Dependencies (..))

-- | Effect to get the 'ExternalPackageState'.
data HasExternalPackageState :: Effect where
  GetExternalPackageState :: HasExternalPackageState m ExternalPackageState

type instance DispatchOf HasExternalPackageState = Dynamic

-- | Get the 'ExternalPackageState'.
getExternalPackageState
  :: HasExternalPackageState :> es
  => Eff es ExternalPackageState
getExternalPackageState = send GetExternalPackageState

-- | Effect to get the 'InstEnvs'.
data HasInstEnvs :: Effect where
  GetInstEnvs :: HasInstEnvs m InstEnvs

type instance DispatchOf HasInstEnvs = Dynamic

-- | Get the complete type class instance environments.
getInstEnvs :: HasInstEnvs :> es => Eff es InstEnvs
getInstEnvs = send GetInstEnvs

-- | Run the 'HasInstEnvs' effect.
--
-- This will fetch the necessary components from the 'ModGuts'. To provide just
-- the necessary components manually, use 'runHasInstEnvs''.
runHasInstEnvs
  :: HasExternalPackageState :> es
  => ModGuts
  -> Eff (HasInstEnvs : es) a
  -> Eff es a
runHasInstEnvs guts = do
  let local = mg_inst_env guts
  let orphans = mkModuleSet . dep_orphs . mg_deps $ guts
  runHasInstEnvs' local orphans

-- | Run the 'HasInstEnvs' effect.
--
-- This requires only the necessary components to construct the instance
-- environment. In most cases, these should directly come from the current
-- 'ModGuts'. Prefer to use 'runHasInstEnv', which fetches these values from
-- the current module.
runHasInstEnvs'
  :: HasExternalPackageState :> es
  => InstEnv
  -- ^ Local type class instance environment.
  -> ModuleSet
  -- ^ Visible orphan instances.
  -> Eff (HasInstEnvs : es) a
  -> Eff es a
runHasInstEnvs' local orphans = interpret_ $ \GetInstEnvs -> do
  global <- eps_inst_env <$> getExternalPackageState
  pure InstEnvs
    { ie_local = local
    , ie_global = global
    , ie_visible = orphans
    }

-- | Effect to get the 'FamInstEnvs'.
data HasFamInstEnvs :: Effect where
  GetFamInstEnvs :: HasFamInstEnvs m FamInstEnvs

type instance DispatchOf HasFamInstEnvs = Dynamic

-- | Get the complete type family instance environments.
getFamInstEnvs :: HasFamInstEnvs :> es => Eff es FamInstEnvs
getFamInstEnvs = send GetFamInstEnvs

-- | Run the 'HasFamInstEnvs' effect.
--
-- This will fetch the necessary components from the 'ModGuts'. To provide just
-- the necessary components manually, use 'runHasFamInstEnvs''.
runHasFamInstEnv
  :: HasExternalPackageState :> es
  => ModGuts
  -> Eff (HasFamInstEnvs : es) a
  -> Eff es a
runHasFamInstEnv = runHasFamInstEnv' . mg_fam_inst_env

-- | Run the 'HasFamInstEnvs' effect.
--
-- This requires only the necessary components to construct the instance
-- environment. In most cases, these should directly come from the current
-- 'ModGuts'. Prefer to use 'runHasFamInstEnv', which fetches these values from
-- the current module.
runHasFamInstEnv'
  :: HasExternalPackageState :> es
  => FamInstEnv
  -- ^ Local type family instance environment.
  -> Eff (HasFamInstEnvs : es) a
  -> Eff es a
runHasFamInstEnv' local = interpret_ $ \GetFamInstEnvs -> do
  global <- eps_fam_inst_env <$> getExternalPackageState
  pure (local, global)
