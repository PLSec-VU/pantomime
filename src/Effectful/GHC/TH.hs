{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effectful.GHC.TH
  ( THNameToGHCName (..)
  , thNameToGhcName
  ) where

import Effectful
import Effectful.Dispatch.Dynamic (send)
import Effectful.Error.Static (HasCallStack, Error, throwError)

import GHC.Types.Name (Name)

import Control.Error

import Language.Haskell.TH qualified as TH

data THNameToGHCName :: Effect where
  THNameToGHCName :: TH.Name -> THNameToGHCName m (Maybe Name)

type instance DispatchOf THNameToGHCName = Dynamic

thNameToGhcName
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => THNameToGHCName :> es
  => TH.Name
  -> Eff es Name
thNameToGhcName th = do
  let err = throwError $ LookupError th
  result <- send $ THNameToGHCName th
  maybe err pure result
