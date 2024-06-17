module Types
  ( UC (..)
  , UCGenerated (..)
  , ucGenAnn

  , Bind' (..)
  , CoreBind'
  , nonRec

  , Pass
  ) where

import Data.Data
import GHC.Plugins

-- | The main annotation for this plugin.
newtype UC a = UC
  { observable :: a
  }
  deriving (Data, Typeable, Functor, Traversable, Foldable)

instance Outputable a => Outputable (UC a) where
  ppr (UC obs) = text "UC" <+> ppr obs

-- | An annotation we use to denote binders that were generated for a UC check.
data UCGenerated = UCGenerated
  deriving (Data, Typeable)

-- | Create an annotation to mark that the given binder was generated.
ucGenAnn :: CoreBind' -> Annotation
ucGenAnn (Bind' var _) = Annotation
  { ann_target = NamedTarget $ varName var
  , ann_value = toSerialized serializeWithData UCGenerated
  }

instance Outputable UCGenerated where
  ppr _ = text "UCGenerated"

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
