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
  , MonadThings (..)
  , TyThing (..)
  , lookupIdLocal
  , lookupIdAll
  ) where

import Prelude hiding (break)

import Effectful
import Effectful.Dispatch.Dynamic (send)
import Effectful.Error.Static (HasCallStack, Error, throwError_, runError)
import Effectful.Break

import GHC.Plugins (CoreProgram, Id, Bind (..), varName, dataConWrapId)
import GHC.Core.ConLike (ConLike(..))
import GHC.Types.TyThing (TyThing (..), MonadThings (..))
import GHC.Types.Name (Name)

import Data.Foldable (find, asum)
import Data.Functor ((<&>))

import Control.Error
import Effectful.Context

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

  -- TODO: These functions are not great. I want to throw a different error for
  -- when the TyThing just doesn't match the required type. The problem is that
  -- I don't want 'lookupThing' to have a constraint to this kind of error.
  -- We should just make separate functions for these outside of the typeclass
  -- and have the actual error as part of the interface!
  lookupId name = do
    thing <- lookupThing name
    case thing of
      AnId ident -> pure ident
      AConLike (RealDataCon dataCon) -> pure $ dataConWrapId dataCon
      _ -> throwError_ $ LookupError name

  lookupDataCon name = do
    thing <- lookupThing name
    case thing of
      AConLike (RealDataCon dataCon) -> pure dataCon
      _ -> throwError_ $ LookupError name

  lookupTyCon name = do
    thing <- lookupThing name
    case thing of
      ATyCon tyCon -> pure tyCon
      _ -> throwError_ $ LookupError name

-- | Lookup a local identifier.
lookupIdLocal
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Context Reader CoreProgram :> es
  => Name
  -> Eff es Id
lookupIdLocal name = do
  prog <- get @CoreProgram
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
  => Context Reader CoreProgram :> es
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
