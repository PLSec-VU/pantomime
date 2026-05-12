module Effectful.Cache
  ( Cache
  , cache
  , runCache
  ) where

import Data.Constraint (Dict (..))
import Data.IORef (newIORef, readIORef, writeIORef)
import Effectful (Eff, Effect, Dispatch (..), DispatchOf, IOE, type (:>))
import Effectful.Dispatch.Static
  ( SideEffects (..)
  , StaticRep
  , evalStaticRep
  , unsafeEff_
  )

-- | Effects that can be cached, deferring the effects to be triggered once
-- when the 'Cache' is forced for the first time.
--
-- WARNING: This effect uses 'IORef' under the hood and is thus safe only in
-- single-threaded contexts.
data Cache :: Effect

type instance DispatchOf Cache = Static WithSideEffects

data instance StaticRep Cache = Cache

-- | Cache an effectful computation.
--
-- The effects of this operation will only be run the first time it is forced.
-- On subsequent runs, instead a cached value is returned.
cache :: forall es a. Cache :> es => Eff es a -> Eff es (Eff es a)
cache action = do
  -- NOTE: We don't actually store anything in the effect stack: it exists
  -- solely to capture whether we are allowed to perform this effect. We use it
  -- here to avoid "unused constraint" warnings.
  let _ = Dict @(Cache :> es)
  ref <- unsafeEff_ $ newIORef Nothing
  pure do
    cached <- unsafeEff_ $ readIORef ref
    case cached of
      Just val -> pure val
      Nothing -> do
        val <- action
        unsafeEff_ $ writeIORef ref (Just val)
        pure val

-- | Allows effectful computation to be cached.
runCache :: IOE :> es => Eff (Cache : es) a -> Eff es a
runCache = evalStaticRep Cache
