module Pantomime
  ( plugin
  , Pantomime (..)
  , SymCompare (..)
  , module Pantomime.Combinator
  ) where

import GHC.Plugins hiding (empty, (<>))

import qualified Language.Haskell.TH.Syntax as TH

import Pantomime.Annotation
import Pantomime.Combinator
import Pantomime.Passes
import Pantomime.Monad.GHC

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

install :: MonadCore m => [CommandLineOption] -> [CoreToDo] -> m [CoreToDo]
install _ todo = do
  let symComparePasses =
        [ printAndLintPass @(SymCompare TH.Name)
        , symComparePass
        ]

  let checkSpecPasses =
        [ printAndLintPass @(Pantomime TH.Name)
        , checkSpecPass
        ]

  pure $ mconcat
    [ symComparePasses
    , checkSpecPasses
    , todo
    ]
