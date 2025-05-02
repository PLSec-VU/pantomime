-- TODO: Add module docs.
module Pantomime.Unification
  ( unifyApp
  , unifyApps
  , unifyExprs
  , resolveInstances
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Unify (tcUnifyTys, alwaysBindFun)
import GHC.Core.Map.Type (TypeMap)
import GHC.Core.Predicate (isDictId)
import GHC.Core.InstEnv (InstEnvs, lookupUniqueInstEnv, instanceDFunId)
import GHC.Core.TyCo.Rep (Type (..), Scaled (..), scaledThing)
import GHC.Data.TrieMap (TrieMap (..), insertTM)
import GHC.Data.Maybe (rightToMaybe)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy, substTy)

import Data.Maybe (fromMaybe)

import Control.Applicative (Alternative (..))
import Control.Monad (guard)

import Lens.Micro
import Lens.Micro.Extras (view)

import Pantomime.Util

-- | Mapping used to track information for unification.
data Unification = Unification
  { _substitution :: Subst
  -- ^ The substitution as dictated by a GHC unification.
  , _dictionaries :: TypeMap CoreExpr
  -- ^ The dictionary expressions/variables currently in-scope.
  , _quantifiers :: DTyCoVarSet
  -- ^ The quantifiers currently in use.
  }

-- | An empty unification mapping.
emptyUnif :: Unification
emptyUnif = Unification
  { _substitution = emptySubst
  , _dictionaries = emptyTM
  , _quantifiers = emptyDVarSet
  }

-- | Lens into substitution of the 'Unification'.
substitution :: Lens' Unification Subst
substitution f unif = do
  let rebuild subst = Unification
        { _substitution = subst
        , _dictionaries = _dictionaries unif
        , _quantifiers = _quantifiers unif
        }
  rebuild <$> f (_substitution unif)

-- | Lens into dictionaries of the 'Unification'.
dictionaries :: Lens' Unification (TypeMap CoreExpr)
dictionaries f unif = do
  let rebuild dict = Unification
        { _substitution = _substitution unif
        , _dictionaries = dict
        , _quantifiers = _quantifiers unif
        }
  rebuild <$> f (_dictionaries unif)

-- | Lens into quantifiers of the 'Unification'.
quantifiers :: Lens' Unification DVarSet
quantifiers f unif = do
  let rebuild quants = Unification
        { _substitution = _substitution unif
        , _dictionaries = _dictionaries unif
        , _quantifiers = quants
        }
  rebuild <$> f (_quantifiers unif)

-- | A lens into the 'InScopeSet' of a 'Subst'.
scopeSubst :: Lens' Subst InScopeSet
scopeSubst f (Subst scope' ids tvs cvs) = do
  let rebuild scope'' = Subst scope'' ids tvs cvs
  rebuild <$> f scope'

-- | Lookup a dictionary identifier given a type.
--
-- This will not resolve instances. The purpose of this lookup is to not have
-- duplicate dictionary constraints in a unified expression.
lookupDict
  :: Type
  -> Unification
  -> (CoreExpr, Unification)
lookupDict ty unif = do
  -- Note that we need to use the new type for lookup in order to properly
  -- deduplicate constraints.
  let ty' = substTy (unif ^. substitution) ty

  -- Attempt to get an already existing identifier in the unification map.
  let found = do
        let existing = lookupTM ty' $ unif ^. dictionaries
        (, unif) <$> existing

  -- If it doesn't exists, we create a fresh variable with the appropriate type.
  -- Additionally, we add it to the dictionary map for future unification.
  let new = do
        let scaled = Scaled ManyTy ty'
        let (fresh, unif') = unif
              & substitution . scopeSubst %~~ freshId "dict" scaled

        let fresh' = Var fresh
        let unif'' = unif' & dictionaries %~ insertTM ty' fresh'
        (fresh', unif'')

  -- Attempt to use an existing dictionary, otherwise create a fresh one.
  fromMaybe new found

-- | Multiple lookups using 'lookupDict'.
lookupDicts
  :: Traversable f
  => f Type
  -> Unification
  -> (f CoreExpr, Unification)
lookupDicts = accumL lookupDict

-- | Lookup the unifying type of a type variable.
--
-- This will additionally track the type variables that are used by the new,
-- unified type in the unification map.
lookupTy
  :: TyVar
  -> Unification
  -> (Type, Unification)
lookupTy var unif = do
  let ty = substTyVar (unif ^. substitution) var
  -- Extend the quantifier set if the substitution was a type variable.
  let extend = case ty of
        TyVarTy var' -> flip extendDVarSet var'
        _ -> id
  let unif' = unif & quantifiers %~ extend

  (ty, unif')

-- | Multiple lookups using 'lookupTy'.
lookupTys
  :: Traversable f
  => f TyVar
  -> Unification
  -> (f Type, Unification)
lookupTys = accumL lookupTy

-- | Fetches all free type and dictionary variables.
--
-- The intent for this is to close expressions which we unified using
-- 'applyUnification'.
tyVarsAndDictIds :: Unification -> ([TyVar], [DictId])
tyVarsAndDictIds unif = do
  let tyVars = dVarSetElems $ unif ^. quantifiers
  let select = \case
        Var var | isDictId var && isLocalId var -> (var :)
        _ -> id
  let dictIds = foldTM select (unif ^. dictionaries) []
  (tyVars, dictIds)

-- | Closes an expression using a unification.
--
-- It is assumed that this expression has been first unified using the
-- 'applyUnification'.
closeExpr :: Unification -> CoreExpr -> CoreExpr
closeExpr unif expr = do
  let (tyVars, dictIds) = tyVarsAndDictIds unif
  foldr Lam expr $ tyVars <> dictIds

-- | Split the type of an expression into its components.
splitExprTy :: CoreExpr -> ([TyVar], ThetaType, Type)
splitExprTy = tcSplitSigmaTy . exprType

-- | Unify two types using 'unifyTypes'.
unifyType
  :: Alternative m
  => Monad m
  => Type
  -> Type
  -> m Unification
unifyType lhs rhs = unifyTypes [(lhs, rhs)]

-- | Unify the given types.
--
-- Creates a unification map for use in 'applyUnification'.
unifyTypes
  :: Alternative m
  => Monad m
  => [(Type, Type)]
  -> m Unification
unifyTypes tys = do
  let (lhs, rhs) = unzip tys
  subst <- maybeM $ tcUnifyTys alwaysBindFun lhs rhs
  pure $ Unification subst emptyTM emptyDVarSet

-- | Applies the unification map the the expression.
--
-- This will apply the type variables from the substitution to the expression.
-- Additionally, it will apply dictionary variables. They are tracked in the
-- 'Unification' map to avoid duplicate constraints.
--
-- The returned expression will have free variables as dictated by the
-- unification mapping. However way the expression is used, make sure to
-- eventually close the expression using 'closeExpr'.
applyUnification
  :: CoreExpr
  -> Unification
  -> (CoreExpr, Unification)
applyUnification expr unif = do
  -- Split the type variables and theta type.
  let (tyVars, thetaTy, _) = splitExprTy expr

  -- Get the type arguments and lookup the dictionary variables.
  let (tyArgs, unif') = lookupTys tyVars unif
  let (thetaArg, unif'') = lookupDicts thetaTy unif'

  -- Apply the type arguments and dictionary variables
  let args = fmap Type tyArgs <> thetaArg
  let expr' = foldl' App expr args

  -- Return the updated unification map and expression with the appropriate
  -- unification variables applied.
  (expr', unif'')

-- | Multiple applications of the unification via 'applyUnification'.
applyUnifications
  :: Traversable f
  => f CoreExpr
  -> Unification
  -> (f CoreExpr, Unification)
applyUnifications = accumL applyUnification

-- | A single unifying application using 'unifyApps'.
unifyApp
  :: Alternative m
  => Monad m
  => CoreExpr
  -> CoreArg
  -> m CoreExpr
unifyApp fun arg = unifyApps fun [arg]

-- | Application that unifies polymorphic types.
--
-- This will apply the given arguments to the spine. Any type or dictionary
-- variables that occur prior any of the body type are unified and placed as
-- outer type and dictionary variables.
unifyApps
  :: Alternative m
  => Monad m
  => CoreExpr
  -> [CoreArg]
  -> m CoreExpr
unifyApps fun args = do
  -- Get the base types without type variables or theta type of all expressions.
  let bodyTy = view _3 . splitExprTy
  let funTy = bodyTy fun
  let argTys = bodyTy <$> args

  -- Create a unification mapping.
  -- TODO: Can we just ignore the multiplicity on this application?
  let (argTysRequired, _) = splitFunTys funTy & _1 . mapped %~ scaledThing
  let pairs = zip argTysRequired argTys
  guard $ length pairs == length argTys
  unif <- unifyTypes pairs

  -- Perform apply unification.
  let (fun', unif') = applyUnification fun unif
  let (args', unif'') = applyUnifications args unif'

  -- Apply the function to the argument. The type and dictionary variables are
  -- still free in this expression.
  let open = mkApps fun' args'

  -- Close the expression by binding the type and dictionary variables.
  pure $ closeExpr unif'' open

-- | Unify two expressions.
--
-- This can be used to compare two expressions that are quantified different,
-- but are otherwise comparable.
unifyExprs
  :: Alternative m
  => Monad m
  => CoreExpr
  -> CoreExpr
  -> m (CoreExpr, CoreExpr)
unifyExprs lhs rhs = do
  -- Get the unifiable part of the type.
  let bodyTy = view _3 . splitExprTy
  let lhsTy = bodyTy lhs
  let rhsTy = bodyTy rhs

  -- Get a unification mapping.
  unif <- unifyType lhsTy rhsTy

  -- Apply the unification for both expressions.
  let (lhs', unif') = applyUnification lhs unif
  let (rhs', unif'') = applyUnification rhs unif'

  -- Close both expressions.
  let lhs'' = closeExpr unif'' lhs'
  let rhs'' = closeExpr unif'' rhs'

  pure (lhs'', rhs'')

-- | Lookup a class instance in the instantiation environment.
--
-- This will return a dictionary instance as core expression.
lookupClassInst
  :: Alternative m
  => Monad m
  => InstEnvs
  -> Type
  -> m CoreExpr
lookupClassInst env ty = do
  -- Get the typeclass constructor of this type, if possible.
  (tyCon, tyArgs) <- maybeM $ splitTyConApp_maybe ty
  tyClass <- maybeM $ tyConClass_maybe tyCon

  -- Get the instance for this typeclass with supplied types, if possible.
  let eitherInst = lookupUniqueInstEnv env tyClass tyArgs
  (clsInst, tys) <- maybeM $ rightToMaybe eitherInst

  -- Create an expression for the instance.
  let dict = Var $ instanceDFunId clsInst
  pure $ mkApps dict (Type <$> tys)

-- | Instantiate dictionaries in a core expression.
--
-- Notably, this will only instantiate if a unique option exists for the
-- instance. GHC will generally not by itself miss a resolvable instance of a
-- typeclass. Instead, this function is intended to be used together with other
-- unification-like functions in this module, as these unifications can create
-- resolvable typeclass constraints.
resolveInstances
  :: InstEnvs
  -> CoreExpr
  -> CoreExpr
resolveInstances env expr = do
  -- Get a mapping from constraints to instances.
  let theta = splitExprTy expr ^. _2
  let instances = zip theta $ theta <&> lookupClassInst env

  -- Convert this mapping into a trie map.
  let extend key val = alterTM key (val <|>)
  let dicts = foldl' (flip $ uncurry extend) emptyTM instances

  -- Set this dictionary for a unification.
  let unif = emptyUnif & dictionaries .~ dicts

  -- Apply the unification using the resolved instances and close it.
  let (expr', unif') = applyUnification expr unif
  closeExpr unif' expr'
