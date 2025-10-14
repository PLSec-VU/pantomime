module Pantomime.Subst
  ( Subst
  , mkEmptySubst
  , extendSubst
  , extendSubstMany
  , extendIdSubst
  , extendIdSubstMany
  , lookupIdSubst
  , substTy
  , substTyVar
  , substCo
  ) where

import Pantomime.Expr
import Pantomime.Result

import GHC.Core.Type qualified as GHC
import GHC.Stack (HasCallStack)
import GHC.Plugins
  ( Var
  , Id
  , TyVar
  , CvSubstEnv
  , TvSubstEnv
  , IdEnv
  , InScopeSet
  , emptyInScopeSet
  , emptyVarEnv
  , isTyVar
  , isCoVar
  , extendVarEnv
  , lookupVarEnv
  , isId
  )

import Control.Monad (foldM)

-- | A substitution map for 'Expr'.
--
-- Note, it is strickingly similar to the GHC Substitution. The main difference
-- is the lookup for identifiers, which will look up a symbolic expression.
data Subst es where
  Subst ::
    { scSubst :: InScopeSet
    , idSubst :: IdEnv (EvalExpr es)
    , tvSubst :: TvSubstEnv
    , cvSubst :: CvSubstEnv
    } -> Subst es

-- | An empty substitution map.
mkEmptySubst :: Subst es
mkEmptySubst = Subst
  { scSubst = emptyInScopeSet
  , idSubst = emptyVarEnv
  , tvSubst = emptyVarEnv
  , cvSubst = emptyVarEnv
  }

-- | Extend the substitution with the given mapping.
extendSubst
  :: HasCallStack
  => () !> es
  => Subst es
  -> Var
  -> Arg es
  -> Result es (Subst es)
extendSubst subst var arg = if
  | isTyVar var -> do
    -- Ensure that the variables are only types. Note that we force the
    -- evaluation here as type reduction should always terminate.
    ty <- forceTy arg

    -- Extend the type variable substitution.
    let tvSubst' = extendVarEnv (tvSubst subst) var ty
    pure subst { tvSubst = tvSubst' }

  | isCoVar var -> do
    -- Ensure that the variables are only types. Note that we force the
    -- evaluation here as type reduction should always terminate.
    co <- forceCo arg

    -- Extend the coercion variable substitution.
    let cvSubst' = extendVarEnv (cvSubst subst) var co
    pure subst { cvSubst = cvSubst' }

  | otherwise -> do
    -- Extend the identifier substitution.
    let idSubst' = extendVarEnv (idSubst subst) var arg
    pure subst { idSubst = idSubst' } 

-- | Extend the substitution with the given mappings.
extendSubstMany
  :: HasCallStack
  => () !> es
  => Foldable f
  => Subst es
  -> f (Var, Arg es)
  -> Result es (Subst es)
extendSubstMany = foldM $ uncurry . extendSubst

-- | Extend the identifier substitution with the given mapping.
extendIdSubst
  :: HasCallStack
  => () !> es
  => Subst fs
  -> Id
  -> EvalExpr fs
  -> Result es (Subst fs)
extendIdSubst subst var arg = if
  | isId var -> do
    -- Extend the identifier substitution.
    let idSubst' = extendVarEnv (idSubst subst) var arg
    pure subst { idSubst = idSubst' }
  | otherwise -> throw ()

-- | Extend the identifier substitution with the given mappings.
extendIdSubstMany
  :: HasCallStack
  => () !> es
  => Foldable f
  => Subst fs
  -> f (Id, EvalExpr fs)
  -> Result es (Subst fs)
extendIdSubstMany = foldM $ uncurry . extendIdSubst

-- | Lookup a variable in the current substitution environment.
lookupIdSubst
  :: Subst es
  -> Id
  -> Maybe (EvalExpr es)
lookupIdSubst = lookupVarEnv . idSubst

-- | Substitute a Type.
substTy
  :: Subst es
  -> Type
  -> Type
substTy subst ty = do
  let subst' = tyCoSubst subst
  GHC.substTy subst' ty

-- | Substitute a TyVar.
substTyVar
  :: Subst es
  -> TyVar
  -> Type
substTyVar subst tv = do
  let subst' = tyCoSubst subst
  GHC.substTyVar subst' tv

-- | Substitute a Coercion.
substCo
  :: Subst es
  -> Coercion
  -> Coercion
substCo subst ty = do
  let subst' = tyCoSubst subst
  GHC.substCo subst' ty

-- | Get a GHC Substitution than can be used for type and coercion substitution.
tyCoSubst :: Subst es -> GHC.Subst
tyCoSubst Subst { .. } = GHC.Subst scSubst emptyVarEnv tvSubst cvSubst
