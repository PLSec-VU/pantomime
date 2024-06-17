module Util
  ( maybeM
  , unwrap
  , (??=)

  , freshLocalVar
  , freshGlobalVar

  , resolveTH
  , thNameToGhcName'

  , polyApp
  ) where

import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad ((>=>))

import GHC.MonadCore
import GHC.Plugins hiding (empty, (<>))
import GHC.Types.TyThing (lookupId)
import GHC.Core.Unify (tcUnifyTy)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy, substTy)

import Data.Maybe (mapMaybe, listToMaybe)

import qualified Language.Haskell.TH.Syntax as TH

import Types

-- | Convert the given maybe into an alternative.
maybeM :: Alternative m => Maybe a -> m a
maybeM = maybe empty pure

-- | Unwrap the given monad, calling fail if the computation failed.
unwrap :: MonadFail m => MaybeT m a -> String -> m a
unwrap m str = runMaybeT m >>= \case
  Just a -> return a
  Nothing -> fail str

infixl 0 ??=

-- | An infix version of [`unwrap`].
(??=) :: MonadFail m => MaybeT m a -> String -> m a
(??=) = unwrap

-- | Creates a fresh variable.
freshLocalVar :: MonadCore m => String -> Type -> m Var
freshLocalVar name ty = do
  unique <- liftCore getUniqueM
  let name' = mkSystemName unique $ mkVarOcc name
  let var = mkLocalVar VanillaId name' ManyTy ty vanillaIdInfo
  return var

-- | Creates a fresh variable.
freshGlobalVar :: MonadCore m => String -> Type -> m Var
freshGlobalVar name ty = do
  unique <- liftCore getUniqueM
  let name' = mkSystemName unique $ mkVarOcc name
  let var = mkGlobalVar VanillaId name' ty vanillaIdInfo
  return var

-- | Resolves all the binders in the UC structure.
resolveTH :: (Alternative m, MonadCore m) => CoreProgram -> TH.Name -> m CoreBind'
resolveTH prog = thNameToGhcName' >=> toCorebind
  where
    toCorebind name = findInProgram prog name <|> getUnfolding name

-- | Attempts to convert a template haskell name into a Core name. Wrapper of
-- `thNameToGhcName`, but made polymorphic on the monad.
thNameToGhcName' :: (Alternative m, MonadCore m) => TH.Name -> m Name
thNameToGhcName' = liftCore . thNameToGhcName >=> maybeM

-- | Retrieves a CoreBind corresponding to a Name from the given CoreProgram.
-- Only retrieves non-recursive bindings.
findInProgram :: Alternative m => CoreProgram -> Name -> m CoreBind'
findInProgram prog name = maybeM $ firstJust cmp prog
  where
    firstJust f = listToMaybe . mapMaybe f
    cmp = \case
      NonRec x e | varName x == name -> Just $ Bind' x e
      _ -> Nothing

-- | Fetches the unfolding of a name as a corebind.
getUnfolding :: (Alternative m, MonadCore m) => Name -> m CoreBind'
getUnfolding name = do
  id' <- liftCore $ lookupId name
  let unfolding = idUnfolding id'
  case unfolding of
    CoreUnfolding { uf_tmpl = expr } -> return $ Bind' id' expr
    _ -> empty

-- | Apply the given expressions, handling both type abstractions and 
-- constraint abstractions that may exist before either of the expressions.
--
-- This will fail if the first argument was not a function, or if we could not
-- unify the actual argument type with the required type.
polyApp :: (Alternative m, MonadCore m) => CoreExpr -> CoreExpr -> m CoreExpr
polyApp fExpr aExpr = do
  -- Split the quantifiers and typeclass constraints from the type
  let splitTy = tcSplitSigmaTy . exprType
  let (fTyVars, fPiTys, funTy) = splitTy fExpr
  let (aTyVars, aPiTys, argTy) = splitTy aExpr

  -- Get the required argument type, that is, the given argument needs to be of
  -- this type.
  (_, _, argTyRequired, _) <- maybeM $ splitFunTy_maybe funTy

  -- Try to unify the required argument with the actual argument type.
  subst@(Subst _ _ tvSubst _) <- maybeM $ tcUnifyTy argTyRequired argTy

  -- Converts a type variable into its corresponding type application. The
  -- only thing this does is use the unified version of said type variable if
  -- it exists. Otherwise, we just return the original type variable as is.
  let toTyArg :: TyVar -> CoreExpr
      toTyArg tyVar = Type $ case lookupVarEnv tvSubst tyVar of
        Just ty -> ty
        _ -> mkTyVarTy tyVar

  -- Converts a predicate type to an argument, using the unification
  -- substitution map to get the correct type of this argument.
  let toPiArg :: MonadCore m => PredType -> m CoreExpr
      toPiArg pty = do
        let pty' = substTy subst pty
        var <- freshLocalVar "constraint" pty'
        return $ Var var

  -- Applies both type variables and typeclass constraints to the given
  -- expression. These applied arguments occur free in the expression after
  -- running this function.
  let apply :: MonadCore m => [TyVar] -> [PredType] -> CoreExpr -> m CoreExpr
      apply tyVars piTys expr = do
        let tyArgs = toTyArg <$> tyVars
        piArgs <- toPiArg `mapM` piTys
        let expr' = foldl App expr $ tyArgs <> piArgs
        return expr'

  -- Perform the necessary type and typeclass applications to the function
  -- and argument expression. We use the resulting expressions to form an
  -- application. Note that the types and typeclass we applied are still free
  -- in the expression.
  fExpr' <- apply fTyVars fPiTys fExpr
  aExpr' <- apply aTyVars aPiTys aExpr
  let expr = App fExpr' aExpr'

  -- Adjusts the type of the typeclass variables to match the unification.
  let adjustTy var = do
        let ty = substTy subst $ varType var
        setVarType var ty

  -- Get the free type variables and typeclass in the expression. Map them to
  -- match the unification.
  let tyVarsAndPiTys = adjustTy <$> exprFreeVarsList expr

  -- Now we introduce abstractions for all the free variables, making the
  -- expression well-formed.
  return $ foldr Lam expr tyVarsAndPiTys
