{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- TODO: There are quite a few more effects we should write for the external
-- package registry. For now, we will extend it on a by need basis.

module Effectful.GHC.External
  ( ExtPackages (..)
  , getExtPackages
  , runExtAll

  , ExtInstEnv (..)
  , getExtInstEnv
  , runExtInstEnv
  , getInstEnvs

  , ExtFamInstEnv (..)
  , getExtFamInstEnv
  , runExtFamInstEnv
  , getFamInstEnvs
  ) where

import Effectful
import Effectful.Dispatch.Dynamic (send, interpret_)

import GHC.Plugins
import GHC.Core.FamInstEnv (FamInstEnv, FamInstEnvs)
import GHC.Core.InstEnv (InstEnv, InstEnvs (..))
import GHC.Unit.External
  ( ExternalPackageState (..)
  , PackageInstEnv
  , PackageFamInstEnv
  )
import GHC.Unit.Module.Deps (Dependencies (..))
import Effectful.Context

-- | Effect to get the complete 'ExternalPackageState'.
data ExtPackages :: Effect where
  ExtPackages :: ExtPackages m ExternalPackageState

type instance DispatchOf ExtPackages = Dynamic

-- | Get the 'ExternalPackageState'.
--
-- This will dispatch the 'ExtPackages' effect.
getExtPackages
  :: ExtPackages :> es
  => Eff es ExternalPackageState
getExtPackages = send ExtPackages

-- | Runner to expose all effects derived from the 'ExtPackages' effect.
runExtAll
  :: ExtPackages :> es
  => Eff (ExtInstEnv : ExtFamInstEnv : es) a
  -> Eff es a
runExtAll = runExtFamInstEnv . runExtInstEnv

-- | Effect to get the external 'InstEnv'.
--
-- The 'InstEnv' contains typeclass instances declared in external modules.
data ExtInstEnv :: Effect where
  ExtInstEnv :: ExtInstEnv m PackageInstEnv

type instance DispatchOf ExtInstEnv = Dynamic

-- | Get the external 'PackageInstEnv'.
--
-- This will dispatch the 'ExtInstEnv' effect.
getExtInstEnv :: ExtInstEnv :> es => Eff es PackageInstEnv
getExtInstEnv = send ExtInstEnv

-- | Run the 'ExtInstEnv' effect through the 'ExtPackages' effect.
runExtInstEnv
  :: ExtPackages :> es
  => Eff (ExtInstEnv : es) a
  -> Eff es a
runExtInstEnv = interpret_ $ \ExtInstEnv -> do
  eps_inst_env <$> getExtPackages

-- | Get the typeclass instance environments.
--
-- Get the complete typeclass instance environments using the effects that
-- fetch the local and global environment. We additionally require the
-- dependencies to gather the visible orphan modules.
getInstEnvs
  :: ExtInstEnv :> es
  => Context Reader InstEnv :> es
  => Context Reader Dependencies :> es
  => Eff es InstEnvs
getInstEnvs = do
  local <- get @InstEnv
  global <- getExtInstEnv
  dependencies <- get @Dependencies
  pure InstEnvs
    { ie_local = local
    , ie_global = global
    , ie_visible = mkModuleSet $ dep_orphs dependencies
    }

-- | Effect to get the external 'FamInstEnv'.
--
-- The 'FamInstEnv' contains type-family instances declared in external modules.
data ExtFamInstEnv :: Effect where
  ExtFamInstEnv :: ExtFamInstEnv m PackageFamInstEnv

type instance DispatchOf ExtFamInstEnv = Dynamic

-- | Get the external 'PackageFamInstEnv'.
--
-- This will dispatch the 'ExtFamInstEnv' effect.
getExtFamInstEnv :: ExtFamInstEnv :> es => Eff es PackageFamInstEnv
getExtFamInstEnv = send ExtFamInstEnv

-- | Run the 'ExtInstEnv' effect through the 'ExtPackages' effect.
runExtFamInstEnv
  :: ExtPackages :> es
  => Eff (ExtFamInstEnv : es) a
  -> Eff es a
runExtFamInstEnv = interpret_ $ \ExtFamInstEnv -> do
  eps_fam_inst_env <$> getExtPackages

-- | Get the 'FamInstEnvs'.
--
-- Get the complete type family instance environments using the effects that
-- fetch the local and global environment.
getFamInstEnvs
  :: Context Reader FamInstEnv :> es
  => ExtFamInstEnv :> es
  => Eff es FamInstEnvs
getFamInstEnvs = do
  local <- get @FamInstEnv
  global <- getExtFamInstEnv
  pure (local, global)
