module Pantomime.Subst
  ( Subst
  , dbgIdEnv
  , mkEmptySubst
  , extendSubst
  , extendSubstMany
  , lookupIdSubst
  , substTy
  , substTyVar
  , substCo
  ) where

import Pantomime.Expr

import GHC.Plugins qualified as GHC
import GHC.Utils.Outputable
  ( Outputable (..)
  , SDoc
  )
import GHC.Plugins
  ( Var
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
  )
import Control.Monad (foldM)
import GHC.Core.Type qualified as GHC

-- | A substitution map for 'Expr'.
--
-- Note, it is strickingly similar to the GHC Substitution. The main difference
-- is the lookup for identifiers, which will look up a symbolic expression.
data Subst where
  Subst ::
    { scSubst :: InScopeSet
    , idSubst :: IdEnv (Eval Expr)
    , tvSubst :: TvSubstEnv
    , cvSubst :: CvSubstEnv
    } -> Subst

-- TODO: Remove this one!
dbgIdEnv
  :: Subst
  -> SDoc
dbgIdEnv = ppr . GHC.varEnvDomain . idSubst

-- | An empty substitution map.
mkEmptySubst :: Subst
mkEmptySubst = Subst
  { scSubst = emptyInScopeSet
  , idSubst = emptyVarEnv
  , tvSubst = emptyVarEnv
  , cvSubst = emptyVarEnv
  }

-- | Extend the substitution with the given mapping.
extendSubst
  :: Subst
  -> Var
  -> Arg
  -> Eval Subst
extendSubst subst var arg = if
  | isTyVar var -> do
    -- FIXME: We currently create a new substitution for every type argument
    -- that exists. This might introduce a huge amount of code paths. Consider
    -- for example a data type with 3 existentials, each with two options.
    -- If we case split for every one, we get 8 executions. Likely, only 2 of
    -- those were actually possible in the first place.
    --
    -- The alternatives would be:
    -- 1. Let the tvSubst (and cvSubst) be a Union, so they themselves may
    -- return different values once they're required.
    -- 2. If we really won't ever even rely on this behaviour of having multiple
    -- types in one Union, then we should just check here whether we have
    -- strictly one value! The outer monad should also just be an error one
    -- instead of Eval in this case btw. The current implementation is actually
    -- heavily leaning in this direction!

    -- Ensure that the variables are only types. Note that we force the
    -- evaluation here as type reduction should always terminate.
    ty <- arg >>= \case
      Type ty -> pure ty
      _ -> throwError' ()

    -- Extend the type variable substitution.
    let tvSubst' = extendVarEnv (tvSubst subst) var ty
    pure subst { tvSubst = tvSubst' }

  | isCoVar var -> do
    -- Ensure that the variables are only types. Note that we force the
    -- evaluation here as type reduction should always terminate.
    co <- arg >>= \case
      Coercion co -> pure co
      _ -> throwError' ()

    -- Extend the coercion variable substitution.
    let cvSubst' = extendVarEnv (cvSubst subst) var co
    pure subst { cvSubst = cvSubst' }

  | otherwise -> do
    -- Extend the identifier substitution.
    let idSubst' = extendVarEnv (idSubst subst) var arg
    pure subst { idSubst = idSubst' } 

-- | Extend the substitution with the given mappings.
extendSubstMany
  :: Foldable f
  => Subst
  -> f (Var, Arg)
  -> Eval Subst
extendSubstMany = foldM $ uncurry . extendSubst

-- | Lookup a variable in the current substitution environment.
lookupIdSubst
  :: Subst
  -> Var
  -> Maybe (Eval Expr)
lookupIdSubst = lookupVarEnv . idSubst

-- | Substitute a Type.
substTy
  :: Subst
  -> Type
  -> Type
substTy subst ty = do
  let subst' = tyCoSubst subst
  GHC.substTy subst' ty

-- | Substitute a TyVar.
substTyVar
  :: Subst
  -> TyVar
  -> Type
substTyVar subst tv = do
  let subst' = tyCoSubst subst
  GHC.substTyVar subst' tv

-- | Substitute a Coercion.
substCo
  :: Subst
  -> Coercion
  -> Coercion
substCo subst ty = do
  let subst' = tyCoSubst subst
  GHC.substCo subst' ty

-- | Get a GHC Substitution than can be used for type and coercion substitution.
tyCoSubst :: Subst -> GHC.Subst
tyCoSubst Subst { .. } = GHC.Subst scSubst emptyVarEnv tvSubst cvSubst
