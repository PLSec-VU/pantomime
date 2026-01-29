{-# LANGUAGE DuplicateRecordFields #-}

module Pantomime (
  plugin,
  Theory (..),
  PluginAxioms (..),
  Circuit,
  Pantomime (..),
  pantomime,
  NonInterference (..),
  tickStateCorrespondence,
  projectionCoherence,
  PipelineCorrectness (..),
  pipelineCorrectness,
) where

import GHC.Plugins hiding (empty, (<>))

import Pantomime.Annotation
import Pantomime.Axiom
import Pantomime.Passes

plugin :: Plugin
plugin =
  defaultPlugin
    { installCoreToDos = install
    , pluginRecompile = purePlugin
    }

install ::
  (Applicative m) =>
  [CommandLineOption] ->
  [CoreToDo] ->
  m [CoreToDo]
install _ todo = do
  let validityPasses =
        [ printAndLintPass @Theory
        , checkValidityPass
        ]

  pure $
    mconcat
      [ validityPasses
      , todo
      ]
