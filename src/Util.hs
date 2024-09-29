module Util
  ( maybeM
  , unwrap
  , (??=)

  , fix
  , fuse
  , (<|-|>)

  , freshTyVar
  , freshLocalVar
  , freshGlobalVar

  , resolveTH
  , resolveTH'
  , resolveTH2
  , findLocal
  , nameToCoreBind
  , thNameToGhcName'

  , polyApp
  ) where

import Control.Applicative
import Control.Monad.Trans.Maybe
import Control.Monad ((>=>))
import Control.Monad.Reader (reader)

import GHC.MonadCore
import GHC.Plugins hiding (empty, (<>))
import GHC.Types.TyThing (lookupId)
import GHC.Core.Unify (tcUnifyTy)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy, substTy)

import Data.Maybe (mapMaybe, listToMaybe)
import Data.List (foldl')

import Data.Data
import Generics.SYB hiding (empty)

import qualified Language.Haskell.TH.Syntax as TH

import Types

-- | Run the given pass until a fixed point is reached. That is, the given pass
-- does not produce a new result.
fix :: (MonadCore m, Data a) => Pass (MaybeT m) a -> Pass m a
fix f = everywhereM $ mkM go
  where
    go e = runMaybeT (f e) >>= \case
      Just e' -> fix f e'
      Nothing -> return e

-- | Fuse all the given passes; the first succesful pass wil return its result.
fuse :: Alternative m => [Pass m a] -> Pass m a
fuse = foldl' (<|-|>) $ const empty

-- | Fuses two passes; the first succesful pass will return its result.
(<|-|>) :: Alternative m => Pass m a -> Pass m a -> Pass m a
(<|-|>) p p' e = p e <|> p' e

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

freshTyVar :: MonadCore m => String -> Kind -> m Var
freshTyVar name kind = do
  unique <- liftCore getUniqueM
  let name' = mkSystemName unique $ mkVarOcc name
  let var = mkTyVar name' kind
  return var

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

-- | Resolves a template haskell name to a non-recursive core binder.
resolveTH :: (Alternative m, MonadCore m) => CoreProgram -> TH.Name -> m CoreBind'
resolveTH prog = thNameToGhcName' >=> nameToCoreBind prog

-- | Same as `resolveTH`, but emits an error on failure.
resolveTH' :: (MonadFail m, MonadCore m) => CoreProgram -> TH.Name -> m CoreBind'
resolveTH' prog name = do
  resolveTH prog name
    ??= "Could not resolve function: " <> TH.nameBase name

resolveTH2 :: Alternative m => MonadMod m => MonadCore m => TH.Name -> m CoreBind'
resolveTH2 name = do
  var <- thNameToId name
  expr <- findLocal var <|> getUnfolding' var
  return $ Bind' var expr

-- | Fetches the (non-recursive) core binder corresponding to the name.
nameToCoreBind :: (Alternative m, MonadCore m) => CoreProgram -> Name -> m CoreBind'
nameToCoreBind prog name = findInProgram prog name <|> getUnfolding name

-- | Attempts to convert a template haskell name into a Core name. Wrapper of
-- `thNameToGhcName`, but made polymorphic on the monad.
thNameToGhcName' :: (Alternative m, MonadCore m) => TH.Name -> m Name
thNameToGhcName' = liftCore . thNameToGhcName >=> maybeM

thNameToId :: Alternative m => MonadCore m => TH.Name -> m Id
thNameToId = thNameToGhcName' >=> liftCore . lookupId

-- | Retrieves a CoreBind corresponding to a Name from the given CoreProgram.
-- Only retrieves non-recursive bindings.
findInProgram :: Alternative m => CoreProgram -> Name -> m CoreBind'
findInProgram prog name = maybeM $ firstJust cmp prog
  where
    firstJust f = listToMaybe . mapMaybe f
    cmp = \case
      NonRec x e | varName x == name -> Just $ Bind' x e
      _ -> Nothing

findLocal :: Alternative m => MonadMod m => Id -> m CoreExpr
findLocal var = do
  prog <- reader mg_binds
  let firstJust f = maybeM . listToMaybe . mapMaybe f
  let cmp = \case
        NonRec x e | var == x -> Just $ e
        _ -> Nothing
  firstJust cmp prog

-- | Fetches the unfolding of a name as a corebind.
getUnfolding :: (Alternative m, MonadCore m) => Name -> m CoreBind'
getUnfolding name = do
  id' <- liftCore $ lookupId name
  let unfolding = idUnfolding id'
  case unfolding of
    CoreUnfolding { uf_tmpl = expr } -> return $ Bind' id' expr
    _ -> empty

getUnfolding' :: (Alternative m, MonadCore m) => Id -> m CoreExpr
getUnfolding' var = do
  let unfolding = idUnfolding var
  case unfolding of
    CoreUnfolding { uf_tmpl = expr } -> return expr
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
  -- subst@(Subst inscope idSubst tvSubst cvSubst) <- maybeM $ tcUnifyTy argTyRequired argTy
  -- dbg' "=============================="
  -- dbg $ exprType fExpr
  -- dbg fExpr
  -- dbg' "------------------------------"
  -- dbg $ exprType aExpr
  -- dbg aExpr
  -- dbg' "inscope:"
  -- dbg inscope
  -- dbg' "id:"
  -- dbg idSubst
  -- dbg' "tv:"
  -- dbg tvSubst
  -- dbg' "cv:"
  -- dbg cvSubst
  -- TODO: Really I want to give some Result type here as return. For error
  -- reporting, it would be really nice if it tells us why unification failed
  -- (or with the check above that the first argument was not actually a
  -- function).

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

  -- Get the new type variables and dictionaries from the expression.
  let globals = unionDVarSets $ fmap exprFreeVarsDSet [fExpr, aExpr]
  let tyVarsAndPiArgs = exprFreeVarsDSet expr `minusDVarSet` globals

  -- We introduce abstractions for all the new variables, making the expression
  -- well-formed.
  let expr' = foldr Lam expr $ dVarSetElems tyVarsAndPiArgs
  return expr'
