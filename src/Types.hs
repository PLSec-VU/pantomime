module Types
  ( UC (..)
  , UCGenerated (..)
  , UCNorm (..)
  , ucGenAnn

  , UCCompare (..)
  -- , UCCheck (..)
  -- , mkCheck

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
--
-- Annotation on a circuit with type: s -> i -> (s, o)
data UC a = UC
  { observation :: a
  -- ^ Observation function: o -> o'
  , leakage :: a
  -- ^ Leakage function: i -> i'
  , simulator :: a
  -- ^ Simulator: s' -> i' -> (s', o)
  , projection :: a
  -- ^ State projection: s -> s'
  }
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

instance Outputable a => Outputable (UC a) where
  ppr uc = text "UC" $+$ nest 2 fields
    where
      fields = vcat
        [ text "{" <+> ppr (observation uc)
        , text "," <+> ppr (leakage uc)
        , text "," <+> ppr (simulator uc)
        , text "," <+> ppr (projection uc)
        , text "}"
        ]

newtype UCCompare a = UCCompare a
  deriving (Data, Typeable, Functor, Traversable, Foldable)

data UCNorm = UCNorm
  deriving (Show, Data, Typeable)

-- | An annotation we use to denote binders that were generated for a UC check.
--
-- The checks will perform rewrites that are generally not optimal for codegen.
-- Hence, we create new binders so we can perform rewrites without affecting the
-- final program code. This annotations allows us to track which declarations
-- should eventually be removed.
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

-- | Anything that has module guts.
class HasModGuts a where
  modGuts :: a -> ModGuts

instance HasModGuts ModGuts where
  modGuts = id

-- | Anything that has an in scope set.
class HasInScopeSet a where
  inScopeSet :: a -> InScopeSet

instance HasInScopeSet InScopeSet where
  inScopeSet = id

-- | Anything that tracks an ordering in declarations.
class HasOrderedDecl a where
  orderedDecl :: a -> [CoreBndr]

instance HasOrderedDecl [CoreBndr] where
  orderedDecl = id

-- | Anything that tracks which binders are case binders.
class HasCaseBndrs a where
  caseBndrs :: a -> VarSet
