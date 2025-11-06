{-# LANGUAGE DuplicateRecordFields #-}

module Pantomime
  ( plugin

  , Theory (..)
  , Circuit

  , Pantomime (..)
  , pantomime

  , NonInterference (..)
  , nonInterference0
  , nonInterference1
  ) where

import GHC.Plugins hiding (empty, (<>))

import Pantomime.Annotation
import Pantomime.Passes

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

install
  :: Applicative m
  => [CommandLineOption]
  -> [CoreToDo]
  -> m [CoreToDo]
install _ todo = do
  let validityPasses =
        [ printAndLintPass @Theory
        , checkValidityPass
        ]

  pure $ mconcat
    [ validityPasses
    , todo
    ]
