module Types
  ( SymCompare (..)
  , Spec (..)

  , Pass
  , Bind' (..)
  , CoreBind'
  , nonRec

  , HasModGuts (..)
  , HasModGuts' (..)
  , HasRuleEnv (..)
  ) where

import GHC.Plugins

import Data.Data

import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Reader (MonadReader (..), ReaderT)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (StateT)
import Control.Monad.Trans.Maybe (MaybeT)

-- | Leakage specification of a circuit.
--
-- Annotation should be on a circuit of type: Circuit si i o
-- TODO: At some point this type should replace the original UC annotation and
-- we should remove the prime on the field names.
-- TODO: Rebrand this to a Pantomime annotation.
data Spec a = Spec
  { observation :: a
  -- ^ Observation: Circuit so o o'
  , leakage :: a
  -- ^ Leakage: Circuit sl i a
  , simulator :: a
  -- ^ Simulator: Circuit ss a o'
  , projection :: a
  -- ^ State Projection: (si, so) -> (sl, ss)
  }
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

instance Outputable a => Outputable (Spec a) where
  ppr spec = text "UC" $+$ nest 2 fields
    where
      fields = vcat
        [ text "{" <+> ppr (observation spec)
        , text "," <+> ppr (leakage spec)
        , text "," <+> ppr (simulator spec)
        , text "," <+> ppr (projection spec)
        , text "}"
        ]

-- TODO: Maybe remove the Sym part. We should also rebrand this to a Pantomime
-- named operation perhaps?
newtype SymCompare a = SymCompare a
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

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
-- get rid of this file or clean it up!
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
