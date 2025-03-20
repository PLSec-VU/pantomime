{-# OPTIONS_GHC -Wno-orphans #-}
module GHC.MonadCore
  ( MonadCore (..)
  , dbg
  , dbg'
  ) where

import GHC.Plugins (CoreM, Outputable, debugTraceMsg, ppr, text)

import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Reader (ReaderT)
import Control.Monad.Trans.Writer (WriterT)
import Control.Monad.Trans.State (StateT)
import Control.Monad.Trans.Except (ExceptT)
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
  fail msg = liftIO $ ioError (userError msg)

-- | Debug print GHC structures in a CoreM monad stack.
dbg :: (MonadCore m, Outputable o) => o -> m ()
dbg = liftCore . debugTraceMsg . ppr

-- | Debug print a string in a CoreM monad stack.
dbg' :: MonadCore m => String -> m ()
dbg' = liftCore . debugTraceMsg . text
