module Effectful.GHC.ModGuts
  ( ModGutsEs
  , runModGuts
  ) where

import Effectful
import Effectful.Reader.Static (Reader, runReader)
import GHC.Core (CoreProgram)
import GHC.Core.InstEnv (InstEnv)
import GHC.Core.FamInstEnv (FamInstEnv)
import GHC.Unit.Module.ModGuts (ModGuts (..))
import GHC.Unit.Module.Deps (Dependencies)

type ModGutsEs es =
  ( Reader InstEnv :> es
  , Reader FamInstEnv :> es
  , Reader CoreProgram :> es
  , Reader Dependencies :> es
  -- TODO: Remove this once we don't depend on it anymore!
  , Reader ModGuts :> es
  )

runModGuts
  :: ModGuts
  -> Eff (Reader InstEnv : Reader FamInstEnv : Reader CoreProgram : Reader Dependencies : Reader ModGuts : es) a
  -> Eff es a
runModGuts guts
  -- TODO: Remove this once we don't depend on it anymore!
  = runReader guts
  . runReader (mg_deps guts)
  . runReader (mg_binds guts)
  . runReader (mg_fam_inst_env guts)
  . runReader (mg_inst_env guts)
