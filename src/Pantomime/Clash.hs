{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
module Pantomime.Clash
  ( clashInterp
  ) where

import GHC.Plugins

import qualified Pantomime.Clash.BitVector as BitVector
import qualified Pantomime.Clash.Unsigned as Unsigned
import qualified Pantomime.Clash.Signed as Signed
import qualified Pantomime.Clash.Bit as Bit

import Pantomime.MonadEval
import Pantomime.Value
import Pantomime.WordSize

clashInterp
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m [(Var, Value m ws)]
clashInterp = concat <$> sequence
  [ BitVector.clashInterp
  , Unsigned.clashInterp
  , Signed.clashInterp
  , Bit.clashInterp
  ]
