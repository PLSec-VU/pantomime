module Subst
  ( Class (..)
  , lookupId
  , bndrs
  , extend
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

-- | Anything that can perform a substitution.
class Class s where
  -- | Create an empty substitution, with the given in-scope set.
  new :: InScopeSet -> s

  -- | Lens into the in-scope set of this substitution.
  scope :: Lens' s InScopeSet

  -- | Substitute a binder.
  --
  -- This will ensure the given binder is fresh.
  bndr :: CoreBndr -> s -> (CoreBndr, s)

  -- | Substitute recursive binders.
  --
  -- Ideally, we make this a non-typeclass function. The problem is that GHC
  -- doesn't expose `substIdBndr`, which would be required to put in this
  -- interface in order to make recBndrs non-typeclass.
  recBndrs :: Traversable f => f CoreBndr -> s -> (f CoreBndr,  s)

  -- | Lookup an Id in the substitution.
  lookupId' :: s -> Id -> Maybe CoreExpr

  -- | Extend a substitution.
  extend' :: Var -> CoreArg -> s -> s

  -- | We should actually expose lookups for coercions and types instead of
  -- these directly. We can implement these functions generically then for all
  -- substitutions. There is no use-case so far, hence we keep it like this.
  ty :: s -> Type -> Type

  -- | We should actually expose lookups for coercions and types instead of
  -- these directly. We can implement these functions generically then for all
  -- substitutions. There is no use-case so far, hence we keep it like this.
  co :: s -> Coercion -> Coercion

-- | Lookup an Id in the substitution.
--
-- It may return the variable if no substitution exists. Can panic if the
-- variable was not in scope.
lookupId :: Class s => s -> Id -> CoreExpr
lookupId subst var
  | assertPpr (isId var && not (isCoVar var)) (ppr var)
    not (isLocalId var) = Var var
  | Just expr <- lookupId' subst var = expr
  | Just var' <- subst ^. scope . to (`lookupInScope` var) = Var var'
  | otherwise = pprPanic "lookupId" $ ppr var $$ ppr (subst ^. scope)

-- | Extend the substitution.
--
-- This will additionally extend the in-scope set with the variable, if the
-- `Unique` was not in use previously. While the occurrence of this variable
-- itself is not interesting, we wish to store that its `Unique` is in use. This
-- way, we can generate fresh variables that will not be substituted using the
-- in-scope set of this substitution.
extend :: Class s => Var -> CoreArg -> s -> s
extend var arg subst = do
  let extendScope var' scope'
        | elemInScopeSet var' scope' = scope'
        | otherwise = extendInScopeSet scope' var'
  subst
    & scope %~ extendScope var
    & extend' var arg

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
extendBind (NonRec bndr' expr) = extend bndr' expr
extendBind (Rec pairs) = extendMany pairs

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

-- | Base GHC substitution.
type Base = Subst

instance Class Base where
  new = mkEmptySubst

  scope f (Subst scope' ids tvs cvs) = do
    let rebuild scope'' = Subst scope'' ids tvs cvs
    rebuild <$> f scope'

  bndr = swap .: flip substBndr

  recBndrs = swap .: flip substRecBndrs

  lookupId' = lookupIdSubst_maybe

  extend' var arg subst = extendSubst subst var arg

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

instance Outputable Ordered where
  ppr subst = vcat
    [ subst ^. base . to ppr
    , subst ^. order . to ppr
    ]

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

  lookupId' subst = subst ^. base . to lookupId'

  extend' var arg subst = subst & base %~ extend' var arg

  ty = ty . view base

  co = co . view base

-- | Compare two variables.
--
-- The comparison is based on the definition order of tracked by the substition
-- map.
compareVar :: Ordered -> Var -> Var -> Ordering
compareVar subst x y = do
  -- Finds the index of an id, if it exists
  let idIndex = subst ^. order . to (flip elemIndex)

  -- Sort variables based on their declaration.
  case (idIndex x, idIndex y) of
    (Nothing, Nothing) -> compare x y
    (idx, idx') -> compare idx idx'
