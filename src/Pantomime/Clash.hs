{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
module Pantomime.Clash
  ( clashInterp
  ) where

import GHC.Plugins

import Pantomime.Clash.BitVector qualified as BitVector
import Pantomime.Clash.Unsigned qualified as Unsigned
import Pantomime.Clash.Signed qualified as Signed
import Pantomime.Clash.Bit qualified as Bit

import Pantomime.MonadEval
import Pantomime.Value
import Pantomime.WordSize

import Language.Haskell.TH qualified as TH

import Effectful
import Effectful.Error.Static (Error)
import Effectful.GHC.TH
import Effectful.GHC.TyThing

clashInterp
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es [(Var, Value (Eff es) ws)]
clashInterp = concat <$> sequence
  [ BitVector.clashInterp
  , Unsigned.clashInterp
  , Signed.clashInterp
  , Bit.clashInterp
  ]
