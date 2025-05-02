module Pantomime
  ( plugin
  , SymCompare (..)
  , Spec (..)
  , Projection.Circuit
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.MonadCore

import qualified Language.Haskell.TH.Syntax as TH

import qualified Projection
import Types
import Pantomime.Passes

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

install :: MonadCore m => [CommandLineOption] -> Pass m [CoreToDo]
install _ todo = pure $ mconcat
  [ symComparePasses
  , checkSpecPasses
  , todo
  ]
  where
    symComparePasses =
      [ printAndLintPass @(SymCompare TH.Name)
      , symComparePass
      ]

    checkSpecPasses =
      [ printAndLintPass @(Spec TH.Name)
      , checkSpecPass
      ]
