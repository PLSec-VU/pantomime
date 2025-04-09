{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
module Symbolic.Clash
  ( clashInterp
  )
where

import qualified Symbolic.Clash.BitVector as BitVector
import qualified Symbolic.Clash.Unsigned as Unsigned
import qualified Symbolic.Clash.Signed as Signed
import GHC.Plugins
import Symbolic.Clash.Numeric
import Symbolic.MonadEval
import Symbolic.Value
import Symbolic.WordSize

clashInterp ::
  forall m ws.
  (MonadFail m) =>
  (MonadEval m) =>
  (KnownWordSize ws) =>
  m [(Var, Value m ws)]
clashInterp =
  concat <$> sequence
      [ BitVector.clashInterp
      , Unsigned.clashInterp
      , Signed.clashInterp
      ]
