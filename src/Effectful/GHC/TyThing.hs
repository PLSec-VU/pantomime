{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effectful.GHC.TyThing
  ( LookupThing (..)
  ) where

import Effectful
import Effectful.Dispatch.Dynamic (send)

import GHC.Types.TyThing (TyThing, MonadThings (..))
import GHC.Types.Name (Name)

data LookupThing :: Effect where
  LookupThing :: Name -> LookupThing m TyThing

type instance DispatchOf LookupThing = Dynamic

-- | WARNING: Although canonical, this is an orphan instance. This might clash
-- with other effects that define instances for it.
instance LookupThing :> es => MonadThings (Eff es) where
  lookupThing = send . LookupThing

-- TODO: I guess this should go in a different file, but I want to have
-- effects for outputting stuff. Preferably split that effect into debug stuff
-- and non-debug emitting.
-- TODO: I also want an effect for looking up GHC Names from Template Haskell
-- names.
