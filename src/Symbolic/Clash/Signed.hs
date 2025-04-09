{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}

module Symbolic.Clash.Signed
  ( clashInterp
  ) where

import GHC.Plugins

import Symbolic.Value

clashInterp
  :: forall m ws
   . Monad m
  => m [(Var, Value m ws)]
clashInterp = pure []
