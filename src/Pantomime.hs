module Pantomime
  ( plugin
  , Pantomime (..)
  , SymCompare (..)
  , Projection.Circuit
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.MonadCore

import qualified Language.Haskell.TH.Syntax as TH

import qualified Projection
import Pantomime.Annotation
import Pantomime.Passes

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

install :: MonadCore m => [CommandLineOption] -> [CoreToDo] -> m [CoreToDo]
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
      [ printAndLintPass @(Pantomime TH.Name)
      , checkSpecPass
      ]
