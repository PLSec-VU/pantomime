{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Prune
  ( loopy
  , doubleCase
  , share
  ) where

import GHC.Base (noinline)
import Pantomime
import Pantomime.BuiltIn qualified as Pantomime

{-# ANN loopy (Theory mempty) #-}
loopy :: Bool -> Pantomime.Bool
loopy value = Pantomime.boolean do
  let go x = case x of
        True -> True
        False -> go $ not x
  go value

infinite :: a
infinite = noinline infinite

{-# ANN doubleCase (Theory mempty) #-}
doubleCase :: Bool -> Pantomime.Bool
doubleCase value = Pantomime.boolean do
  case value of
    True -> True
    False -> case value of
      True -> infinite
      False -> True

{-# ANN share (Theory mempty) #-}
share :: Bool -> Bool -> Pantomime.Bool
share lhs rhs = Pantomime.boolean do
  let x = case lhs || rhs of
        True -> True
        False -> infinite
  case lhs of
    True -> x
    False -> case rhs of
      True -> x
      False -> True

