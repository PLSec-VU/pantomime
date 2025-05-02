{-# OPTIONS_GHC -Wno-orphans #-}
module Pantomime.Monad.GHC
  ( MonadCore (..)
  , dbg
  , dbg'

  , HasModGuts' (..)
  ) where

import GHC.Plugins (CoreM, Outputable, ModGuts, debugTraceMsg, ppr, text)

import Control.Monad.Trans.Class (MonadTrans (..))
-- import Control.Monad.Reader (ReaderT)
import Control.Monad.Reader (MonadReader (..), ReaderT)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (StateT)
import Control.Monad.Writer (WriterT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.IO.Class (liftIO)

class Monad m => MonadCore m where
  liftCore :: CoreM a -> m a

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

-- FIXME: We should perhaps make a wrapper for CoreM, because this orphan is
-- not so nice...
instance MonadFail CoreM where
  fail = liftIO . ioError . userError

-- | Debug print GHC structures in a CoreM monad stack.
dbg :: (MonadCore m, Outputable o) => o -> m ()
dbg = liftCore . debugTraceMsg . ppr

-- | Debug print a string in a CoreM monad stack.
dbg' :: MonadCore m => String -> m ()
dbg' = liftCore . debugTraceMsg . text

-- TODO: Remove prime on name of typeclass and function.
-- | Anything Monad that has module guts.
class Monad m => HasModGuts' m where
  modGuts' :: m ModGuts

-- instance HasModGuts' m => HasModGuts' (ReaderT r m) where
--   modGuts' = lift modGuts'

-- TODO: I think this instance is ugly. We should create a monad that contains
-- whatever we need instead.
instance Monad m => HasModGuts' (ReaderT ModGuts m) where
  modGuts' = reader id

instance (Monoid w, HasModGuts' m) => HasModGuts' (WriterT w m) where
  modGuts' = lift modGuts'

instance HasModGuts' m => HasModGuts' (StateT s m) where
  modGuts' = lift modGuts'

instance HasModGuts' m => HasModGuts' (MaybeT m) where
  modGuts' = lift modGuts'

instance HasModGuts' m => HasModGuts' (ExceptT e m) where
  modGuts' = lift modGuts'

