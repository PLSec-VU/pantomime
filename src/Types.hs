{-# LANGUAGE OverloadedStrings #-}

module Types
  ( Pass
  , Bind' (..)
  , CoreBind'
  , nonRec

  , HasModGuts (..)
  , HasModGuts' (..)
  , HasRuleEnv (..)
  ) where

import GHC.Plugins

import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Reader (MonadReader (..), ReaderT)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (StateT)
import Control.Monad.Trans.Maybe (MaybeT)

-- | An always non-recursive binder.
data Bind' a = Bind' a (Expr a)

-- | Transform an always non-recursive binder into a normal binder.
nonRec :: Bind' a -> Bind a
nonRec (Bind' x e) = NonRec x e

instance OutputableBndr a => Outputable (Bind' a) where
  ppr (Bind' x e) = ppr $ NonRec x e

-- | A core binder that is non-recursive.
type CoreBind' = Bind' CoreBndr

-- | A pass transforms some value of type a inside of monad m.
type Pass m a = a -> m a

-- | Anything that has module guts.
class HasModGuts a where
  modGuts :: a -> ModGuts

instance HasModGuts ModGuts where
  modGuts = id

-- TODO: We should just have this as only version. Also, we should probably
-- get rid of this file or clean it up! I think these should go into
-- Pantomime.Monad
-- | Anything Monad that has module guts.
class Monad m => HasModGuts' m where
  modGuts' :: m ModGuts

instance (Monad m, HasModGuts r) => HasModGuts' (ReaderT r m) where
  modGuts' = reader modGuts

instance HasModGuts' m => HasModGuts' (ExceptT e m) where
  modGuts' = lift modGuts'

instance HasModGuts' m => HasModGuts' (StateT s m) where
  modGuts' = lift modGuts'

instance HasModGuts' m => HasModGuts' (MaybeT m) where
  modGuts' = lift modGuts'

-- | Anything that has a rule environment.
class HasRuleEnv a where
  ruleEnv :: a -> RuleEnv

instance HasRuleEnv RuleEnv where
  ruleEnv = id
