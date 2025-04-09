{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
module Symbolic.Clash.Signed
  ( clashInterp
  ) where

import Clash.Prelude (Signed)
import Clash.Sized.Internal.Signed((+#), (-#), (*#), negate#, fromInteger#)

import GHC.Plugins
import GHC.Types.TyThing (lookupId, MonadThings (..))
import GHC.MonadCore
import GHC.TypeLits
import GHC.Builtin.Types.Prim (alphaTyVar)

import Control.Monad.Except (MonadError(..))

import Data.Typeable (cast, Proxy (..))

import Grisette.Unified (EvalModeTag (..))
import Grisette

import Util

import Symbolic.Value
import Symbolic.MonadEval
import Symbolic.Runtime
import Symbolic.Util
import Symbolic.WordSize

clashInterp
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m [(Var, Value m ws)]
clashInterp = undefined
  --sequence
  --[ interpAdd
  --, interpSub
  --, interpMul
  --, interpNeg
  --, interpFromInteger
  --]
