{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effectful.Grisette.Fresh
  ( Fresh (..)
  , MonadFresh (..)
  , FreshIndex (..)
  , Identifier (..)
  , nextFreshIndex
  , runFresh
  , runFreshWithIndex
  ) where

import Data.Composition ((.:))

import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.Reader.Static (runReader, ask, local)
import Effectful.State.Static.Local (runState, get, put)

import Grisette
  ( MonadFresh (..)
  , FreshIndex (..)
  , Identifier (..)
  , nextFreshIndex
  )

-- | Effect for fresh symbolic value generation.
--
-- This effect is the combination of a reader effect for an 'Identifier' and a
-- state effect for a 'FreshIndex'.
data Fresh :: Effect where
  GetFreshIndex :: Fresh m FreshIndex
  -- ^ Get the current index for fresh variable generation.
  SetFreshIndex :: FreshIndex -> Fresh m ()
  -- ^ Set the current index for fresh variable generation.
  GetIdentifier :: Fresh m Identifier
  -- ^ Get the identifier.
  LocalIdentifier :: (Identifier -> Identifier) -> m a -> Fresh m a
  -- ^ Change the identifier locally and use a new index from 0 locally.

type instance DispatchOf Fresh = Dynamic

-- | WARNING: Although canonical, this is an orphan instance. This might clash
-- with other effects that define instances for it.
instance Fresh :> es => MonadFresh (Eff es) where
  getFreshIndex = send GetFreshIndex
  setFreshIndex = send . SetFreshIndex
  getIdentifier = send GetIdentifier
  localIdentifier = send .: LocalIdentifier

-- | Run the fresh value generation effect.
runFresh
  :: Identifier
  -> Eff (Fresh : es) a
  -> Eff es a
runFresh identifier = fmap fst . runFreshWithIndex identifier (FreshIndex 0)

-- | Run the fresh value generation effect.
runFreshWithIndex
  :: Identifier
  -> FreshIndex
  -> Eff (Fresh : es) a
  -> Eff es (a, FreshIndex)
runFreshWithIndex identifier idx
  = runReader identifier
  . runState idx
  . interpret @Fresh (\env -> \case
    GetFreshIndex -> get
    SetFreshIndex idx' -> put idx'
    GetIdentifier -> ask
    LocalIdentifier f m -> localSeqUnlift env \unlift -> do
      local f $ unlift m)
  . inject
