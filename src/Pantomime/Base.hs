-- TODO: This should go into a separate package!
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
module Pantomime.Base
  ( axioms
  ) where

import GHC.Num.Integer
  ( Integer (..)
  , integerToInt#
  , integerToWord#
  )
import GHC.Num.BigNat (bigNatToWord#)
import GHC.Base
  ( Int#
  , Word#
  , Addr#
  , TYPE
  , raise#
  , word2Int#
  , negateInt#
  , word2Int#
  , int2Word#
  , noinline
  )

import Control.Exception.Base (patError)

import Pantomime.Axiom (PluginAxioms (..))

integerToInt' :: Integer -> Int#
integerToInt' = \case
  IS i -> i
  IP b -> word2Int# $ bigNatToWord# b
  IN b -> negateInt# $ word2Int# $ bigNatToWord# b

integerToWord' :: Integer -> Word#
integerToWord' = \case
  IS i -> int2Word# i
  IP bn -> bigNatToWord# bn
  IN bn -> int2Word# $ negateInt# $ word2Int# $ bigNatToWord# bn

noinline' :: a -> a
noinline' = id

-- FIXME: This is not actually the implementation for 'patError'.
patError' :: forall q (a :: TYPE q). Addr# -> a
patError' _ = raise# ()

axioms :: PluginAxioms
axioms =  PluginAxioms
  { typeAxioms = mempty
  , termAxioms =
    [ ('integerToInt#, 'integerToInt')
    , ('integerToWord#, 'integerToWord')
    , ('noinline, 'noinline')
    , ('patError, 'patError')
    ]
  }
