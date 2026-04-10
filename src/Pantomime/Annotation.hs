{-# LANGUAGE DuplicateRecordFields #-}

module Pantomime.Annotation
  ( Theory (..)
  ) where

import Data.Data (Data)
import Pantomime.Axiom (PluginAxioms)

-- TODO: Not sure I like the name. This checks whether an expression whose
-- result is of type Bool is valid. That is, whether it will always return True.
data Theory where
  Theory :: PluginAxioms -> Theory
  deriving (Show, Data)
