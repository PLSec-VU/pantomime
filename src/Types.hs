module Types
  ( UC (..)
  , UCNorm (..)
  , UCCompare (..)
  , SymCompare (..)
  , Spec (..)

  , UCGenerated (..)
  , ucGenAnn

  , Pass
  , Bind' (..)
  , CoreBind'
  , nonRec

  , HasModGuts (..)
  , HasRuleEnv (..)
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
  -- ^ Leakage function: s1 -> i -> (s1, a)
  , simulator :: a
  -- ^ Simulator: s2 -> a -> (s2, o)
  , projection :: a
  -- ^ State projection: s -> (s1, s2)
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
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

-- | Leakage specification of a circuit.
--
-- Annotation should be on a circuit of type: Circuit si i o
-- TODO: At some point this type should replace the original UC annotation and
-- we should remove the prime on the field names.
data Spec a = Spec
  { observation' :: a
  -- ^ Observation circuit: Circuit so o o'
  , leakage' :: a
  -- ^ Leakage circuit: Circuit sl i a
  , simulator' :: a
  -- ^ Simulator circuit: Circuit ss a o'
  , projection' :: a
  -- ^ State projection: (si, so) -> (sl, ss)
  }
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

newtype SymCompare a = SymCompare a
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

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

-- | Anything that has a rule environment.
class HasRuleEnv a where
  ruleEnv :: a -> RuleEnv

instance HasRuleEnv RuleEnv where
  ruleEnv = id
