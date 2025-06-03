{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Pantomime.Monad.GHC
  ( MonadCore (..)
  , HasModGuts (..)
  , dbg
  , dbg'
  , thNameToGhcName'
  , resolveTH
  , resolveTH'
  , getInstEnvs'
  , getFamInstEnvs'
  ) where

import GHC.Plugins
import GHC.Core.InstEnv (InstEnvs (..))
import GHC.Core.FamInstEnv (FamInstEnvs)
import GHC.Types.TyThing (MonadThings(..))
import GHC.Unit.External (eps_inst_env)

import GHC.Data.Maybe (mapMaybe, listToMaybe)

import qualified Language.Haskell.TH as TH

import Control.Applicative
import Control.Monad ((>=>))
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Reader (MonadReader (reader), ReaderT)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (StateT)
import Control.Monad.Writer (WriterT)
import Control.Monad.Trans.Maybe (MaybeT)

import Grisette (FreshT)

import Effectful
import Effectful.GHC.CoreE qualified as CoreE
import Effectful.Reader.Static (Reader, ask)

import Pantomime.Util

class Monad m => MonadCore m where
  liftCore :: CoreM a -> m a

-- WARNING: This orhpan is the canonical instance the effect instance. We will
-- remove it once we completely swap towards an effect system.
instance (IOE :> es, CoreE.CoreE :> es) => MonadCore (Eff es) where
  liftCore = CoreE.liftCore

instance MonadCore CoreM where
  liftCore = id

instance MonadCore m => MonadCore (MaybeT m) where
  liftCore = lift . liftCore

instance MonadCore m => MonadCore (ReaderT r m) where
  liftCore = lift . liftCore

instance (Monoid w, MonadCore m) => MonadCore (WriterT w m) where
  liftCore = lift . liftCore

instance MonadCore m => MonadCore (StateT s m) where
  liftCore = lift . liftCore

instance MonadCore m => MonadCore (ExceptT s m) where
  liftCore = lift . liftCore

instance MonadCore m => MonadCore (FreshT m) where
  liftCore = lift . liftCore

-- FIXME: We should perhaps make a wrapper for CoreM, because this orphan is
-- not so nice...
instance MonadFail CoreM where
  fail = liftIO . ioError . userError

-- FIXME: This orphan is not nice. We should change it!
instance MonadFail m => MonadFail (FreshT m) where
  fail = lift . fail

-- TODO: Remove prime on name of typeclass and function.
-- | Anything Monad that has module guts.
class Monad m => HasModGuts m where
  modGuts :: m ModGuts

-- instance HasModGuts m => HasModGuts (ReaderT r m) where
--   modGuts = lift modGuts

-- TODO: I think this instance is ugly. We should create a monad that contains
-- whatever we need instead.
instance Monad m => HasModGuts (ReaderT ModGuts m) where
  modGuts = reader id

instance (Monoid w, HasModGuts m) => HasModGuts (WriterT w m) where
  modGuts = lift modGuts

instance HasModGuts m => HasModGuts (StateT s m) where
  modGuts = lift modGuts

instance HasModGuts m => HasModGuts (MaybeT m) where
  modGuts = lift modGuts

instance HasModGuts m => HasModGuts (ExceptT e m) where
  modGuts = lift modGuts

instance HasModGuts m => HasModGuts (FreshT m) where
  modGuts = lift modGuts

instance Reader ModGuts :> es => HasModGuts (Eff es) where
  modGuts = ask

-- | Debug print GHC structures in a CoreM monad stack.
dbg :: MonadCore m => Outputable o => o -> m ()
dbg = liftCore . debugTraceMsg . ppr

-- | Debug print a string in a CoreM monad stack.
dbg' :: MonadCore m => String -> m ()
dbg' = liftCore . debugTraceMsg . text

-- | Resolves a template haskell name to a non-recursive variable.
resolveTH
  :: Alternative m
  => MonadCore m
  => HasModGuts m
  => TH.Name
  -> m Var
resolveTH thName = do
  name <- thNameToGhcName' thName
  asum [lookupLocal name, liftCore $ lookupId name]

-- | Same as `lookupTH`, but emits an error on failure.
resolveTH'
  :: MonadFail m
  => MonadCore m
  => HasModGuts m
  => TH.Name
  -> m Var
resolveTH' name = resolveTH name
  ??= "Could not resolve expression: " ++ TH.nameBase name

-- | Lookup a local non-recursive variable.
lookupLocal
  :: Alternative m
  => HasModGuts m
  => Name
  -> m Var
lookupLocal name = do
  prog <- mg_binds <$> modGuts
  let firstJust f = maybeM . listToMaybe . mapMaybe f
  let cmp' = \case
        NonRec x _ | name == varName x -> Just x
        _ -> Nothing
  firstJust cmp' prog

-- | Attempts to convert a template haskell name into a Core name. Wrapper of
-- `thNameToGhcName`, but made polymorphic on the monad.
thNameToGhcName' :: Alternative m => MonadCore m => TH.Name -> m Name
thNameToGhcName' = liftCore . thNameToGhcName >=> maybeM

-- | Fetch the typeclass instance environments.
--
-- Get the typeclass instance environments from a CoreM pass instead of the
-- typechecker pass.
getInstEnvs'
  :: MonadCore m
  => HasModGuts m
  => m InstEnvs
getInstEnvs' = do
  -- Get the global definitions
  hscEnv <- liftCore getHscEnv
  eps <- liftCore . liftIO $ hscEPS hscEnv
  let global = eps_inst_env eps

  -- Get the local definitions
  local <- mg_inst_env <$> modGuts

  -- Return the instance environments
  return $ InstEnvs
    { ie_global = global
    , ie_local = local
    -- TODO: Get actual visible orphan modules
    , ie_visible = mkModuleSet []
    }

-- | Fetch the type family environments.
--
-- Get the type family instance environments from a CoreM pass instead of the
-- typechecker pass.
getFamInstEnvs'
  :: MonadCore m
  => HasModGuts m
  => m FamInstEnvs
getFamInstEnvs' = do
  local <- mg_fam_inst_env <$> modGuts
  global <- liftCore getPackageFamInstEnv
  pure (local, global)
