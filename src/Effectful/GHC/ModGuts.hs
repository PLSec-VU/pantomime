module Effectful.GHC.ModGuts
  ( ModGutsEs
  , runModGuts
  ) where

import Effectful
import Effectful.Context

import GHC.Core (CoreProgram)
import GHC.Core.InstEnv (InstEnv)
import GHC.Core.FamInstEnv (FamInstEnv)
import GHC.Unit.Module.ModGuts (ModGuts (..))
import GHC.Unit.Module.Deps (Dependencies)

type ModGutsEs es =
  ( Context Reader InstEnv :> es
  , Context Reader FamInstEnv :> es
  , Context Reader CoreProgram :> es
  , Context Reader Dependencies :> es
  -- TODO: Remove this once we don't depend on it anymore!
  , Context Reader ModGuts :> es
  )

runModGuts
  :: ModGuts
  -> Eff (Context Reader InstEnv : Context Reader FamInstEnv : Context Reader CoreProgram : Context Reader Dependencies : Context Reader ModGuts : es) a
  -> Eff es a
runModGuts guts
  -- TODO: Remove this once we don't depend on it anymore!
  = runContextReader guts
  . runContextReader (mg_deps guts)
  . runContextReader (mg_binds guts)
  . runContextReader (mg_fam_inst_env guts)
  . runContextReader (mg_inst_env guts)
