module Unification
  ( polyApp
  , unifyExprs
  ) where

import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad.State (MonadState (..), modify, evalStateT)

import GHC.MonadCore
import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Unify (tcUnifyTy)
import GHC.Core.Map.Type (TypeMap)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy, substTy)
import GHC.Data.TrieMap (lookupTM, insertTM, emptyTM)

import Types
import Util

-- | Application with possibly polymorphic functions.
--
-- Apply the given expressions, handling both type abstractions and  typeclass
-- constraints that may exist before either of the expressions.
--
-- This will fail if the first argument was not a function, or if we could not
-- unify the actual argument type with the required type.
polyApp
  :: Alternative m
  => MonadCore m
  => MonadMod m
  => CoreExpr
  -- ^ Function expression.
  -> CoreExpr
  -- ^ Argument expression.
  -> m CoreExpr
  -- ^ Application of argument to function.
polyApp fun arg = do
  -- Split the quantifiers and typeclass constraints from the type
  let funTy = unifiableType fun
  let argTy = unifiableType arg

  -- Get the required argument type, that is, the given argument needs to be of
  -- this type.
  (_, _, argTyRequired, _) <- maybeM $ splitFunTy_maybe funTy

  -- Try to unify the required argument with the actual argument type.
  subst <- maybeM $ tcUnifyTy argTyRequired argTy
  -- TODO: Really I want to give some Result type here as return. For error
  -- reporting, it would be really nice if it tells us why unification failed
  -- (or with the check above that the first argument was not actually a
  -- function).

  -- Perform the necessary type and typeclass applications to the function
  -- and argument expression. We use the resulting expressions to form an
  -- application. Note that the types and typeclass we applied are still free
  -- in the expression.
  expr <- flip evalStateT emptyTM $ do
    fun' <- applyUnification subst fun
    arg' <- applyUnification subst arg
    return $ App fun' arg'

  -- We introduce abstractions for all the new variables, making the expression
  -- well-formed.
  let tyVarsAndPredArgs = sortQuantVars $ exprFreeVarsList expr
  return $ foldr Lam expr tyVarsAndPredArgs

-- | Unify two expressions.
--
-- This can be used to compare two expressions that are quantified different,
-- but are otherwise comparable.
unifyExprs
  :: Alternative m
  => MonadCore m
  => MonadMod m
  => CoreExpr
  -> CoreExpr
  -> m (CoreExpr, CoreExpr)
unifyExprs lhs rhs = do
  -- Split the quantifiers and typeclass constraints from the type
  let lhsTy = unifiableType lhs
  let rhsTy = unifiableType rhs

  -- Try to unify the lhs with the rhs
  subst <- maybeM $ tcUnifyTy lhsTy rhsTy

  -- Perform apply unfication on both expressions according to the unification.
  (lhs', rhs') <- flip evalStateT emptyTM $ do
    lhs' <- applyUnification subst lhs
    rhs' <- applyUnification subst rhs
    return (lhs', rhs')

  -- Fetch all quantifier variables. Note that we have to fetch the variables
  -- for both expressions as one list. If we do not do this, we may miss some
  -- dictionaries that are used in only one of the expressions. This would make
  -- the unification incorrect!
  let sort = sortQuantVars . nonDetStrictFoldVarSet (:) []
  let quantifiers = sort $ exprFreeVars lhs' <> exprFreeVars rhs'

  -- We introduce abstractions for all the new variables, making the expression
  -- well-formed.
  let lhs'' = foldr Lam lhs' quantifiers
  let rhs'' = foldr Lam rhs' quantifiers
  return (lhs'', rhs'')

-- | Fetch a unifiable type for the given expression.
--
-- Gets the type of the current expression and splits the quantifiers and
-- typeclass constraints from it. When unifying, we want to use this type.
unifiableType :: CoreExpr -> Type
unifiableType expr = ty
  where
    (_, _, ty) = tcSplitSigmaTy $ exprType expr

-- | Applies a unification map to an expression.
--
-- This can be seen as a partial operation when unifying expressions. This
-- function applies all type abstractions and dictionary types with a unified
-- version. The returned expression will have free variables as dictated by
-- the unification mapping. However way the expression is used, make sure to
-- eventually close the expression by binding these free unification variables.
applyUnification
  :: MonadCore m
  => MonadMod m
  => MonadState (TypeMap Var) m
  -- ^ Store dictionary instances to avoid duplicates.
  => Subst
  -- ^ Unification substitution map.
  -> Pass m CoreExpr
  -- ^ Transformation on the given CoreExpr
applyUnification subst@(Subst _ _ tvSubst _) expr = do
  -- Converts a type variable into its corresponding type application. The
  -- only thing this does is use the unified version of said type variable if
  -- it exists. Otherwise, we just return the original type variable as is.
  let toTyArg :: TyVar -> CoreExpr
      toTyArg tyVar = Type $ case lookupVarEnv tvSubst tyVar of
        Just ty -> ty
        _ -> mkTyVarTy tyVar

  -- Get a dictionary variable for a predicate type. We instantiate fresh
  -- variables when we cannot resolve an instance. Note that we track these
  -- fresh variables in a map to avoid duplicates constraints.
  let toPredArg :: MonadState (TypeMap Var) m => MonadCore m => MonadMod m => PredType -> m CoreExpr
      toPredArg predTy = Var <$> do
        let predTy' = substTy subst predTy
        dict <- runMaybeT $ resolveInstance predTy'
        predMap <- get
        case dict <|> lookupTM predTy' predMap of
          Just var -> return var
          Nothing -> do
            var <- freshLocalVar "constraint" predTy'
            modify $ insertTM predTy' var
            return var

  -- Get the type variables and predicate types that should be unified.
  let splitTy = tcSplitSigmaTy . exprType
  let (tyVars, predTys, _) = splitTy expr

  -- Applies both type variables and typeclass constraints to the given
  -- expression. These applied arguments occur free in the expression after
  -- running this function.
  let tyArgs = toTyArg <$> tyVars
  predArgs <- mapM toPredArg predTys
  let expr' = foldl App expr $ tyArgs <> predArgs
  return expr'

