module Pantomime.Monad.GHC
  ( HasModGuts' (..)
  , HasRuleEnv (..)
  ) where

import GHC.Plugins

import Control.Monad.Trans.Class (MonadTrans (..))
-- import Control.Monad.Reader (ReaderT)
import Control.Monad.Reader (MonadReader (..), ReaderT)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (StateT)
import Control.Monad.Trans.Maybe (MaybeT)

-- TODO: Remove prime on name.
-- | Anything Monad that has module guts.
class Monad m => HasModGuts' m where
  modGuts' :: m ModGuts

-- instance HasModGuts' m => HasModGuts' (ReaderT r m) where
--   modGuts' = lift modGuts'

-- TODO: I think this instance is ugly. We should create a monad that contains
-- whatever we need instead.
instance Monad m => HasModGuts' (ReaderT ModGuts m) where
  modGuts' = reader id

instance HasModGuts' m => HasModGuts' (ExceptT e m) where
  modGuts' = lift modGuts'

instance HasModGuts' m => HasModGuts' (StateT s m) where
  modGuts' = lift modGuts'

instance HasModGuts' m => HasModGuts' (MaybeT m) where
  modGuts' = lift modGuts'

-- TODO: Make this into a monad, without the reader part.
-- | Anything that has a rule environment.
class HasRuleEnv a where
  ruleEnv :: a -> RuleEnv

instance HasRuleEnv RuleEnv where
  ruleEnv = id
