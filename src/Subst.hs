module Subst
  ( Class (..)
  , bndrs
  , extendMany
  , extendBind
  , extendProg
  , tick

  , Base
  , Ordered
  , compareVar
  ) where

import GHC.Plugins hiding ((<>))
import GHC.Core.TyCo.Subst (substTy)
import GHC.Types.Tickish (CoreTickish, GenTickish (Breakpoint))

import Data.Composition ((.:))
import Data.Foldable (foldl', toList)
import Data.Function ((&))
import Data.List (elemIndex)
import Data.Maybe (mapMaybe)
import Data.Tuple (swap)

import Lens.Micro (Lens', (%~), to, (^.))
import Lens.Micro.Extras (view)

import Util (accumL, (%~~))

-- TODO: I guess we should just keep the ordering of the original functions.
-- It seems to be nicer to first write the substitution and then the other
-- stuff. It's also how the current code is written! Also, maybe we can remove
-- all the subst stuff from the function names? It seems like we'll be writing
-- qualified syntax anyway? Let's give this some thought!
class Class a where
  -- | Create an empty substitution, with the given in-scope set.
  new :: InScopeSet -> a

  -- | Lens into the in-scope set of this substitution.
  scope :: Lens' a InScopeSet

  -- | Substitute a binder.
  --
  -- This will ensure the given binder is fresh.
  bndr :: CoreBndr -> a -> (CoreBndr, a)

  -- | Substitute recursive binders.
  --
  -- Ideally, we make this a non-typeclass function. The problem is that GHC
  -- doesn't expose `substIdBndr`, which would be required to put in this
  -- interface in order to make recBndrs non-typeclass.
  recBndrs :: Traversable f => f CoreBndr -> a -> (f CoreBndr,  a)

  -- | Lookup an Id in the substitution.
  --
  -- It may return the variable if no substitution exists. Can panic if the
  -- variable was not in scope.
  lookupId :: a -> Id -> CoreExpr

  -- | Extend a substitution.
  --
  -- Compared to `extendSubst` as provided by GHC, this should additionally
  -- extend the in-scope set. This is important when deshadowing names.
  extend :: Var -> CoreArg -> a -> a

  -- | We should actually expose lookups for coercions and types instead of
  -- these directly. We can implement these functions generically then for all
  -- substitutions. There is no use-case so far, hence we keep it like this.
  ty :: a -> Type -> Type

  -- | We should actually expose lookups for coercions and types instead of
  -- these directly. We can implement these functions generically then for all
  -- substitutions. There is no use-case so far, hence we keep it like this.
  co :: a -> Coercion -> Coercion

-- | Substitute multiple binders.
--
-- This will call `bndr` for every binder and accumulate the substitution.
bndrs
  :: Traversable f
  => Class s
  => f CoreBndr
  -> s
  -> (f CoreBndr, s)
bndrs = accumL bndr

-- | Extend with multiple mappings.
--
-- Extend the substitution with multiple variable/expression pairs via a
-- cumulative call of `extend`.
extendMany
  :: Foldable f
  => Class s
  => f (Var, CoreArg)
  -> s
  -> s
extendMany = flip . foldl' . flip $ uncurry extend

-- | Extend the substitution with a binder.
--
-- That is, this will cause the substitution to replace any variable occurence
-- with its definition.
extendBind :: Subst.Class s => CoreBind -> s -> s
extendBind (NonRec bndr' expr) = Subst.extend bndr' expr
extendBind (Rec pairs) = Subst.extendMany pairs

-- | Extend the substitution with a program.
--
-- This is essentially a fold over `extendBind`.
extendProg :: Subst.Class s => CoreProgram -> s -> s
extendProg = flip . foldl' . flip $ extendBind

tick :: Class s => s -> CoreTickish -> CoreTickish
tick subst = \case
  Breakpoint ext n ids -> do
    let go = getIdFromTrivialExpr_maybe . lookupId subst
    Breakpoint ext n $ mapMaybe go ids

  other -> other

type Base = Subst

instance Class Base where
  new = mkEmptySubst

  scope f (Subst scope' ids tvs cvs) = do
    let rebuild scope'' = Subst scope'' ids tvs cvs
    rebuild <$> f scope'

  bndr = swap .: flip substBndr

  recBndrs = swap .: flip substRecBndrs

  lookupId = lookupIdSubst

  extend var arg subst = do
    let subst' = subst & scope %~ flip extendInScopeSet var
    extendSubst subst' var arg

  ty = substTy

  co = substCo

data Ordered = Ordered
  { _base :: Base
  , _order :: [Var]
  }

base :: Lens' Ordered Base
base f (Ordered b o) = do
  let rebuild = flip Ordered o
  rebuild <$> f b

order :: Lens' Ordered [Var]
order f (Ordered b o) = do
  let rebuild = Ordered b
  rebuild <$> f o

compareVar :: Ordered -> Var -> Var -> Ordering
compareVar subst x y = do
  -- Finds the index of an id, if it exists
  let idIndex = subst ^. order . to (flip elemIndex)

  -- Sort variables based on their declaration.
  case (idIndex x, idIndex y) of
    (Nothing, Nothing) -> compare x y
    (idx, idx') -> compare idx idx'

instance Class Ordered where
  new s = Ordered
    { _base = new s
    , _order = []
    }

  scope = base . scope

  bndr var subst = do
    subst
      -- Extend the ordering
      & order %~ (var :)
      -- Substitute the binder in the base substitution
      & base %~~ bndr var

  recBndrs vars subst = do
    subst
      -- Extend the ordering
      & order %~ (toList vars <>)
      -- Substitute the binders in the base substitution
      & base %~~ recBndrs vars

  lookupId subst = subst ^. base . to lookupId

  extend var arg subst = subst & base %~ extend var arg

  ty = ty . view base

  co = co . view base
