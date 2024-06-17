{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}

module UC
  ( plugin
  , UC (..)
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Lint
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.Map.Expr

import GHC.MonadCore

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (foldl', nubBy)
import Data.Maybe (fromJust, catMaybes)

-- import Data.Dynamic
import Data.Data
import Generics.SYB hiding (empty)

import Control.Applicative ((<|>), empty, Alternative (..))
import Control.Monad (guard, forM, foldM)
import Control.Monad.Trans.Maybe

import qualified Language.Haskell.TH.Syntax as TH

import qualified Projection
import Types
import Util

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

-- TODO: Change printUCGenerated to printAnnotated, which should take a type
-- parameter.
install :: MonadCore m => [CommandLineOption] -> Pass m [CoreToDo]
install _ todo = return $ passes <> todo
  where
    passes =
      [ CoreDoPluginPass "CreateUCBinds" createUCBinds
      -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
      , CoreDoPluginPass "InlineAll" inlineAll
      , CoreDoPluginPass "DedupCases" dedupCases
      -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
      -- , CoreLiberateCase
      , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
      , CoreDoPluginPass "RemoveUCBinds" removeUCBinds
      ]

createUCBinds :: (MonadFail m, MonadCore m) => Pass m ModGuts
createUCBinds guts = do
  -- FIXME: We should check that there exists strictly one annotation per bind
  -- and that all of them are non-recursive.
  (_, anns) <- liftCore $ getFirstAnnotations @(UC TH.Name) deserializeWithData guts

  -- Map the template haskell names in the UC structure to a CoreBind.
  let mapMNonDet m uniqfm = getNonDet <$> mapM m (NonDetUniqFM uniqfm)
  let resolveUC = mapM (resolveTH $ mg_binds guts)
  anns' <- mapMNonDet resolveUC anns
    ??= "Could not resolve names bound in UC annotation"

  -- Runs the function on the given CoreBind, given that the CoreBind is
  -- non-recursive.
  let withAnn :: Monad m => (UC CoreBind' -> CoreBind' -> m b) -> CoreBind -> m (Maybe b)
      withAnn f = \case
        NonRec x e -> do
          let ann = lookupUFM anns' $ varName x
          forM ann (flip f $ Bind' x e)
        _ -> return Nothing

  maybeBinds <- forM (mg_binds guts) $ withAnn (projectOutput $ mg_binds guts)
  let binds' = catMaybes maybeBinds
  let binds = nonRec <$> binds'
  let generated = ucGenAnn <$> binds'

  -- Return the guts with the additional binders.
  return guts
    { mg_binds = binds <> mg_binds guts
    , mg_anns = generated <> mg_anns guts
    }

-- | Generates an output projected version of the given binder using the
-- observation function passed by the UC binder.
projectOutput :: (MonadFail m, MonadCore m) => CoreProgram -> UC CoreBind' -> Pass m CoreBind'
projectOutput prog uc (Bind' _ expr) = do
  -- Fetch the CoreExpr of the output projection function.
  Bind' _ oproj <- resolveTH prog 'Projection.oproj
    ??= "Could not fetch output projection function"

  -- Fetch the observation function.
  let Bind' _ obs = observable uc

  -- Apply the output projection on the expression, using the given observation
  -- function.
  expr' <- occurAnalyseExpr <$> foldM polyApp oproj [obs, expr]
    ??= "Incompatible types on observation/implementation pair"

  -- Create a fresh binder for the newly created projection.
  var <- freshGlobalVar "ucgenerated" $ exprType expr'
  return $ Bind' var expr'

-- | Run the given pass on all UC annotated binds.
ucBindsPass :: MonadCore m => Pass m CoreBind' -> Pass m ModGuts
ucBindsPass pass guts = do
  (_, anns) <- liftCore $ getFirstAnnotations @UCGenerated deserializeWithData guts

  binds <- forM (mg_binds guts) $ \case
    NonRec x e | Just _ <- lookupUFM anns $ varName x -> nonRec <$> pass (Bind' x e)
    b -> return b

  return guts { mg_binds = binds }

inlineAll :: MonadCore m => Pass m ModGuts
inlineAll = ucBindsPass $ \(Bind' x e) -> do
  let fused = fuse
        [ betaReduce
        , inlineUnfolding
        , caseDistribute
        , foldCase
        , redundantCase
        ]

  e' <- occurAnalyseExpr <$> fix fused e
  return $ Bind' x e'

printUCGenerated :: MonadCore m => Pass m ModGuts
printUCGenerated = ucBindsPass $ \bind -> do
  dflags <- liftCore getDynFlags
  let cfg = initLintConfig dflags []
  let res = lintCoreBindings' cfg [nonRec bind]
  dbg bind
  dbg res
  return bind
  
-- TODO: Implement this!
removeUCBinds :: MonadCore m => Pass m ModGuts
removeUCBinds guts = do
  return guts

dedupCases :: MonadCore m => Pass m ModGuts
dedupCases = ucBindsPass $ \(Bind' x e) -> do
  e' <- occurAnalyseExpr <$> dedupCase Map.empty e
  return $ Bind' x e'

-- | Run the given pass until a fixed point is reached. That is, the given pass
-- does not produce a new result.
fix :: (MonadCore m, Data a) => Pass (MaybeT m) a -> Pass m a
fix f = everywhereM $ mkM go
  where
    go e = runMaybeT (f e) >>= \case
      Just e' -> fix f e'
      Nothing -> return e

-- | Fuse all the given passes.
fuse :: Alternative m => [Pass m CoreExpr] -> Pass m CoreExpr
fuse = foldl' fuse' $ const empty

-- | Fuses two passes; the first succesful pass will return its result.
fuse' :: Alternative m => Pass m CoreExpr -> Pass m CoreExpr -> Pass m CoreExpr
fuse' p p' e = p e <|> p' e

-- | Beta reduction
betaReduce :: (Alternative m, Monad m) => Pass m CoreExpr
betaReduce = \case
  -- Normal beta reduction.
  App (Lam bind body) arg -> substitute body bind arg

  -- Reduction on let binding.
  Let (NonRec bind expr) body -> substitute body bind expr

  _ -> empty
  where
    -- | substitute e1 x e2 = e1[x:=e2]
    substitute :: Monad m => CoreExpr -> CoreBndr -> CoreExpr -> m CoreExpr
    substitute body bind expr = do
      let inScope = mkInScopeSet $ exprFreeVars body `unionVarSet` exprFreeVars expr
      let subst = extendSubst (mkEmptySubst inScope) bind expr
      let body' = substExpr subst body
      return body'

inlineUnfolding :: (Alternative m, Monad m) => Pass m CoreExpr
inlineUnfolding = \case
  Var x | CoreUnfolding { uf_tmpl = expr } <- idUnfolding x -> return expr
  _ -> empty

-- | Reduces a case expression if the spine of the scrutinee is a constructor.
foldCase :: (Alternative m, Monad m) => Pass m CoreExpr
foldCase = \case
  Case scrut bind _ alts -> do
    -- Get the spine if it is a constructor.
    (ac, es) <- splitCon scrut

    -- Get the alt matching this spine.
    Alt _ bs rhs <- maybeM $ findAlt ac alts

    -- Get the variables that are in scope already.
    let inscope = mkInScopeSet $ unionVarSets
          [ exprFreeVars rhs
          , exprFreeVars scrut
          , mkVarSet bs
          ]

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, the binder should be substituted by the scrutinee.
    let errmsg = "arguments on constructor should be equivalent to binders in pattern"
    let mapping = (bind, scrut) : zipEqual errmsg bs es

    -- Make the substition using the mapping.
    let subst = extendSubstList (mkEmptySubst inscope) mapping

    -- Perform the substitution.
    return $ substExpr subst rhs

  _ -> empty
  where
    -- | Get the constructor spine (if available) of this expression with all
    -- the arguments that are applied to it.
    splitCon expr = do
      let (fun, args) = collectArgs expr

      -- Try to get the AltCon (if possible).
      con <- case fun of
        Var v | isDataConWorkId v -> return $ DataAlt (idDataCon v)
        Lit l -> return $ LitAlt l
        _ -> empty

      -- Trim the type arguments that do not appear on the match.
      let args' = trimConArgs con args
      return (con, args')

-- | Distrubte expressions over a case. This pushes case expressions towards the
-- root of the expression.
caseDistribute :: (Alternative m, MonadCore m) => Pass m CoreExpr
caseDistribute = \case
  -- Nested case
  Case cas@(Case {}) bind ty alts -> do
    temp <- freshOneShotVar $ exprType cas
    let fun = Lam temp (Case (Var temp) bind ty alts)
    distribute fun cas

  -- Inline argument into case
  App cas@Case {} arg -> do
    temp <- freshOneShotVar $ exprType cas
    let fun = Lam temp (App (Var temp) arg)
    distribute fun cas

  -- Inline function into case
  App fun cas@Case {} -> distribute fun cas

  _ -> empty
  where
    distribute fun = \case
      Case scrut bind _ alts -> do
        -- Create a temporary unique variable. We will substitute this variable
        -- for the given function using substExpr, which will make sure that all
        -- the variable renaming is correctly handled.
        temp <- freshOneShotVar $ exprType fun

        -- Distribute the temporary variable as the function to every rhs.
        let distribute' (Alt c bs rhs) = Alt c bs (App (Var temp) rhs)
        let alts' = distribute' <$> alts

        -- Get the type for the new case statement and create the new case.
        let ty = coreAltsType alts'
        let expr = Case scrut bind ty alts'

        -- Get all variables that are in scope
        let inscope = mkInScopeSet $ exprFreeVars expr `unionVarSet` exprFreeVars fun

        -- Use the in-scope set to make a substitution from the temporary
        -- argument to the given function.
        let subst = extendSubst (mkEmptySubst inscope) temp fun

        -- Substitute the temporary variable for the given function.
        return $ substExpr subst expr

      _ -> empty

    -- Creates a temporary var that should be used for a single substitution.
    -- Substituting this temporary variable via substExpr makes sure that
    -- variable renaming is handled correctly. Otherwise, we must take great
    -- care to avoid variable capture.
    freshOneShotVar ty = do
      temp <- freshLocalVar "temp" ty
      let info = setOneShotInfo vanillaIdInfo OneShotLam
      return $ lazySetIdInfo temp info

-- | Removes obselete cases. That is, cases whose result will not change
-- depending on the value of the scrutinee.o
redundantCase :: (Alternative m, Monad m) => Pass m CoreExpr
redundantCase = \case
  Case scrut bind _ alts -> do
    -- Check if all alts are equivalent
    let cmp (Alt _ _ rhs) (Alt _ _ rhs') = eqCoreExpr rhs rhs'
    let equal = length (nubBy cmp alts) == 1

    -- Check if all alts do not bind any of their pattern (which would make
    -- them not equivalent due to different binding variables).
    let uses (Alt _ bs rhs) = exprFreeVars rhs `disjointVarSet` mkVarSet bs
    let unbound = all uses alts

    -- Check if the case is indeed redundant. That is, all alts are equal and
    -- they don't bind the variables in the pattern.
    guard (equal && unbound)

    -- Take the rhs of first alt (since they're all equivalent, and alts is
    -- non-empty).
    let (Alt _ _ expr) = head alts

    -- Get all free variables in this expression for the in-scope set.
    let inscope = mkInScopeSet $ exprFreeVars expr

    -- Use the in-scope set to make a substitution for the scrutinee.
    let subst = extendSubst (mkEmptySubst inscope) bind scrut

    -- Perform the substitution.
    return $ substExpr subst expr

  _ -> empty

-- FIXME: I think there is an issue with the fold given a default branch:
-- we cannot always fold a branch in this case I think. Maybe we could do
-- something like include it in the outer case?
--
-- Occurence check already makes sure that we use the binder in a case instead
-- of another copy of the scrutinized expression. As such, the key in the Map
-- can actually be a variable instead of an expression.
dedupCase :: Monad m => Map CoreBndr (AltCon, [CoreBndr]) -> Pass m CoreExpr
dedupCase scruts = \case
  -- We have case split over this scrutinee if we enter this case. Thus, we can
  -- remove the case split by selecting the branch that was taken previously.
  -- We take care of the binders in the term to reference the outer case.
  Case (Var scrut) bind _ alts | Just (c, bs) <- Map.lookup scrut scruts -> do
    -- A matching alt should always be available.
    let Alt _ bs' rhs = fromJust $ findAlt c alts

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, the binder should be substituted by the scrutinee.
    let mapping = (bind, Var scrut) : zip bs' (Var <$> bs)

    -- Get the inscope variables.
    let inscope = mkInScopeSet $ exprFreeVars rhs

    -- Make the substition using the mapping and perform the substitution.
    let subst = extendSubstList (mkEmptySubst inscope) mapping

    -- Substitute the alts in the expression.
    let expr = substExpr subst rhs

    -- Attempt to fold more cases in the new expression.
    dedupCase scruts expr

  -- We have not case split over this scrutinee before, thus we add it to the
  -- map and continue. We do not have to traverse the scrutinee itself for the
  -- fold in this scenario, as the case distribute pass makes sure that no
  -- scrutinee can contain a case.
  Case scrut bind ty alts -> do
    let withAlt (Alt c bs rhs) = do
          -- We remove the occurence info (may occur many times), as it may do
          -- so after deduplicating a case. The occurence analysis doesn't catch
          -- case, so we do it manually.
          let bs' = flip setIdOccInfo noOccInfo <$> bs
          let scruts' = Map.insert bind (c, bs') scruts
          rhs' <- dedupCase scruts' rhs
          return $ Alt c bs rhs'

    Case scrut bind ty <$> mapM withAlt alts

  e -> gmapM (mkM $ dedupCase scruts) e
