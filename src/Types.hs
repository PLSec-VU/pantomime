module Types
  ( UC (..)
  , UCGenerated (..)
  , UCNorm (..)
  , ucGenAnn

  , UCCompare (..)
  -- , UCCheck (..)
  -- , mkCheck

  , UCTactic (..)
  , Projection (..)

  , Bind' (..)
  , CoreBind'
  , nonRec

  , Pass

  , HasModGuts (..)
  , HasInScopeSet (..)
  , HasOrderedDecl (..)
  , HasCaseBndrs (..)
  ) where

import Data.Data
import GHC.Plugins

-- | Tactic based UC check.
data UCTactic a = UCTactic
  { observation :: a
  -- ^ Observation function: o -> o'
  , leakage :: a
  -- ^ Leakage function: i -> i'
  , simulator :: a
  -- ^ Simulator: s' -> i' -> (s', o)
  , projections :: [Projection a]
  -- ^ State projections.
  }
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

-- | State projection.
--
-- Transform a circuit: s -> i -> (s, o) 
-- To a circuit: s' -> i -> (s', o)
data Projection a = Projection
  { ignore :: a
  -- ^ State ignore function: s -> s'
  , circuit :: a
  -- ^ Simulator for state projection: s' -> i -> (s', o)
  }
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

newtype UCCompare a = UCCompare a
  deriving (Data, Typeable, Functor, Traversable, Foldable)

data UCNorm = UCNorm
  deriving (Show, Data, Typeable)

-- | The main annotation for this plugin.
newtype UC a = UC
  { observable :: a
  }
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

instance Outputable a => Outputable (UC a) where
  ppr (UC obs) = text "UC" <+> ppr obs

-- | An annotation we use to denote binders that were generated for a UC check.
-- In general, the checks will perform rewrites that are generally not optimal
-- for codegen. Hence, we create new binders so we can perform rewrites without
-- affecting the eventual program synthesis.
newtype UCGenerated a = UCGenerated a
  deriving (Show, Data, Typeable)

-- | Create an annotation to mark that the given binder was generated.
ucGenAnn :: Data a => a -> CoreBind' -> Annotation
ucGenAnn x (Bind' var _) = Annotation
  { ann_target = NamedTarget $ varName var
  , ann_value = toSerialized serializeWithData (UCGenerated x)
  }

instance Outputable a => Outputable (UCGenerated a) where
  ppr x = text "UCGenerated:" <+> ppr x

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

class HasModGuts a where
  modGuts :: a -> ModGuts

instance HasModGuts ModGuts where
  modGuts = id

class HasInScopeSet a where
  inScopeSet :: a -> InScopeSet

instance HasInScopeSet InScopeSet where
  inScopeSet = id

class HasOrderedDecl a where
  orderedDecl :: a -> [CoreBndr]

instance HasOrderedDecl [CoreBndr] where
  orderedDecl = id

class HasCaseBndrs a where
  caseBndrs :: a -> VarSet
