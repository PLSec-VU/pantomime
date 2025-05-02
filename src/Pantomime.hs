module Pantomime
  ( plugin
  , Pantomime (..)
  , SymCompare (..)
  , module Pantomime.Combinator
  ) where

import GHC.Plugins hiding (empty, (<>))

import qualified Language.Haskell.TH.Syntax as TH

import Pantomime.Combinator
import Pantomime.Annotation
import Pantomime.Passes
import Pantomime.Monad.GHC

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
