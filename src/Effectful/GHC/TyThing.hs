{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effectful.GHC.TyThing
  ( HasThings (..)
  , LookupError (..)
  , lookupIdLocal
  , lookupIdAll
  ) where

import Prelude hiding (break)

import Effectful
import Effectful.Dispatch.Dynamic (send)
import Effectful.Error.Static (HasCallStack, Error, throwError_, runError)
import Effectful.Reader.Static (Reader, ask)
import Effectful.Break

import GHC.Plugins (CoreProgram, Id, Bind (..), varName)
import GHC.Types.TyThing (TyThing, MonadThings (..))
import GHC.Types.Name (Name)

import Data.Foldable (find, asum)
import Data.Functor ((<&>))

import Control.Error

-- | Effect drop-in for 'MonadThings'.
data HasThings :: Effect where
  LookupThing :: Name -> HasThings m (Maybe TyThing)

type instance DispatchOf HasThings = Dynamic

-- | WARNING: Although canonical, this is an orphan instance. This might clash
-- with other effects that define instances for it.
instance (Error (LookupError Name) :> es, HasThings :> es) => MonadThings (Eff es) where
  lookupThing name = do
    let err = throwError_ $ LookupError name
    result <- send $ LookupThing name
    maybe err pure result

-- | Lookup a local identifier.
lookupIdLocal
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Reader CoreProgram :> es
  => Name
  -> Eff es Id
lookupIdLocal name = do
  prog <- ask @CoreProgram
  let match = (== name) . varName
  let result = asum $ prog <&> \case
        NonRec x _ | match x -> pure x
        Rec bs | Just (x, _) <- find (match . fst) bs -> pure x
        _ -> Nothing

  let err = throwError_ $ LookupError name
  maybe err pure result

-- | Lookup an identifier in both the local and global environment.
lookupIdAll
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Reader CoreProgram :> es
  => HasThings :> es
  => Name
  -> Eff es Id
lookupIdAll name = runBreak do
  -- Perform the lookup operation, resolving on success.
  let attempt m = do
        let continue = const $ pure ()
        result <- runError @(LookupError Name) m
        either continue break result

  -- Attempt to lookup from the global and local namespace.
  attempt $ lookupId name
  attempt $ lookupIdLocal name

  -- All lookups failed. We throw from here, as this is the most sensible
  -- location for the stack trace to end up at.
  throwError_ $ LookupError name
