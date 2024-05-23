{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module UC
  ( plugin
  , UC (..)
  ) where

import GHC.Plugins hiding (empty)
import GHC.Core.Lint
import GHC.Driver.Config.Core.Lint (initLintConfig)

import Data.Bifunctor (second)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (foldl', find, nubBy)
import Data.Maybe (fromJust)

import Data.Data
import Generics.SYB hiding (empty)

import Control.Applicative ((<|>), empty, Alternative (..))
import Control.Monad ((>=>), guard)
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class

data UC = UC
  deriving (Show, Eq, Ord, Data, Typeable)

instance Outputable UC where
  ppr UC = text "UC"

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  -- , pluginRecompile = purePlugin
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  return $ CoreDoPluginPass "Normalize" pass : todo

pass :: ModGuts -> CoreM ModGuts
pass guts = do
  (_, anns) <- getFirstAnnotations @UC deserializeWithData guts

  -- Returns whether a non-recursive bind has the annotation
  let hasAnn :: CoreBind -> Bool
      hasAnn (NonRec b _) = elemUFM_Directly (varUnique b) anns
      hasAnn _ = False

  _ <- bindsOnlyPass (mapM printBind . filter hasAnn) guts
  return guts

printBind :: CoreBind -> CoreM CoreBind
printBind bndr@(NonRec x e) = do
  dflags <- getDynFlags
  e' <- transforms e
  let bndr' = NonRec x e'
  putMsg . ppr $ bndr'

  let cfg = initLintConfig dflags []
  let res = lintCoreBindings' cfg [bndr']
  putMsg . ppr $ res
  return bndr
printBind bndr = return bndr

type FixPass = (CoreExpr -> MaybeT CoreM CoreExpr)

dbg :: Outputable o => o -> MaybeT CoreM ()
dbg = lift . putMsg . ppr

dbg' :: String -> MaybeT CoreM ()
dbg' = lift . putMsgS

transforms :: CoreExpr -> CoreM CoreExpr
transforms = fix fused >=> duplicateCase Map.empty 

fix :: FixPass -> CoreExpr -> CoreM CoreExpr
fix f = everywhereM $ mkM go
  where
    go e = runMaybeT (f e) >>= \case
      Just e' -> fix f e'
      Nothing -> return e

fuse :: [FixPass] -> FixPass
fuse = foldl' fuse' $ const empty

fuse' :: FixPass -> FixPass -> FixPass
fuse' p p' e = p e <|> p' e

fused :: FixPass
fused = fuse
  [ betaReduce
  , caseDistribute
  , foldCase
  , redundantCase
  ]

-- | Beta reduction
betaReduce :: FixPass
betaReduce = \case
  -- Normal beta reduction.
  App (Lam bind body) arg -> return $ substitute body bind arg

  -- Reduction on let binding.
  Let (NonRec bind expr) body -> return $ substitute body bind expr

  _ -> empty
  where
    -- | substitute e1 x e2 = e1[x:=e2]
    substitute :: CoreExpr -> CoreBndr -> CoreExpr -> CoreExpr
    substitute body bind expr = do
      let inScope = mkInScopeSet $ exprFreeVars body `unionVarSet` exprFreeVars expr
      let subst = extendIdSubst (mkEmptySubst inScope) bind expr
      let body' = substExpr subst body
      body'

-- | Reduces a case expression if the spine of the scrutinee is a constructor.
foldCase :: FixPass
foldCase = \case
  Case scrut bind _ alts -> do
    -- Get the spine if it is a constructor.
    (ac, es) <- spine scrut

    -- Remove any type applications, these are never bound by the case.
    let isType = \case
          Type _ -> True
          _ -> False
    let es' = filter (not . isType) es

    -- Get the alt matching this spine.
    Alt _ bs rhs <- matchingAlt alts ac

    -- Get the variables that are in scope already.
    let inscope = mkInScopeSet $ unionVarSets
          [ exprFreeVars rhs
          , exprFreeVars scrut
          , mkVarSet bs
          ]

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, the binder should be substituted by the scrutinee.
    let errmsg = "arguments on constructor should be equivalent to binders in pattern"
    let mapping = (bind, scrut) : zipEqual errmsg bs es'

    -- Make the substition using the mapping.
    let subst = extendIdSubstList (mkEmptySubst inscope) mapping

    -- Perform the substitution.
    return $ substExpr subst rhs

  _ -> empty
  where
    -- | Get the constructor spine (if available) of this expression with all
    -- the arguments that are applied to it.
    spine = \case
      App fun arg -> second (++ [arg]) <$> spine fun
      Var v | isDataConWorkId v -> return (DataAlt (idDataCon v), [])
      Lit l -> return (LitAlt l, [])
      _ -> empty

-- | Distrubte expressions over a case. This pushes case expressions towards the
-- root of the expression.
caseDistribute :: FixPass
caseDistribute = \case
  -- Nested case
  Case cas@(Case {}) bind ty alts -> do
    temp <- tempVar bind $ exprType cas
    let fun = Lam temp (Case (Var temp) bind ty alts)
    distribute fun cas

  -- Inline argument into case
  App cas@(Case _ bind _ _) arg -> do
    temp <- tempVar bind $ exprType cas
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
        temp <- tempVar bind (exprType fun)

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
        let subst = extendIdSubst (mkEmptySubst inscope) temp fun

        -- Substitute the temporary variable for the given function.
        return $ substExpr subst expr

      _ -> empty

    -- Creates a temporary var that should be used for a single substitution.
    -- Substituting this temporary variable via substExpr makes sure that
    -- variable renaming is handled correctly. Otherwise, we must take great
    -- care to avoid variable capture.
    tempVar bind ty = do
        unique <- lift getUniqueM
        let info = setOneShotInfo vanillaIdInfo OneShotLam
        let temp = flip setVarType ty
                 . flip setVarUnique unique
                 . flip lazySetIdInfo info
                 $ bind
        return temp

-- | Removes obselete cases. That is, cases whose result will not change
-- depending on the value of the scrutinee.
redundantCase :: FixPass
redundantCase = \case
  Case scrut bind _ alts -> do
    -- Check if all alts are equivalent
    let cmp (Alt _ _ rhs) (Alt _ _ rhs') = CmpExpr rhs == CmpExpr rhs'
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
    let subst = extendIdSubst (mkEmptySubst inscope) bind scrut

    -- Perform the substitution.
    return $ substExpr subst expr

  _ -> empty

matchingAlt :: Alternative f => [Alt a] -> AltCon -> f (Alt a)
matchingAlt alts ac = maybe empty pure $ matching <|> default'
  where
    matching = find (\(Alt con _ _) -> con == ac) alts
    default' = find (\(Alt con _ _) -> con == DEFAULT) alts

newtype CmpExpr = CmpExpr CoreExpr
  deriving (Data, Typeable)

instance Outputable CmpExpr where
  ppr (CmpExpr e) = ppr e

instance Eq CmpExpr where
  (==) = geq'
    where
      -- Modification of the normal geq in SYB, with a special case for
      -- variables.
      geq' :: GenericQ (GenericQ Bool)
      geq' x y
        | toConstr x == toConstr y = case (cast x, cast y) of
            (Just (v :: Var), Just (v' :: Var)) -> v == v'
            _ -> and (gzipWithQ geq' x y)
        | otherwise = False

instance Ord CmpExpr where
  compare = gcompare'
    where
      -- Modification of the normal gcompare in SYB, with a special case for
      -- variables.
      gcompare' :: (Data a, Data b) => a -> b -> Ordering
      gcompare' x y = case (cast x, cast y) of
        (Just (v :: Var), Just (v' :: Var)) -> compare v v'
        _ -> case (repX, repY) of
          (AlgConstr nX,   AlgConstr nY)   ->
            nX `compare` nY `mappend` mconcat (gzipWithQ gcompare' x y)
          (IntConstr iX,   IntConstr iY)   -> iX `compare` iY
          (FloatConstr rX, FloatConstr rY) -> rX `compare` rY
          (CharConstr cX,  CharConstr cY)  -> cX `compare` cY
          _ -> error "type incompatibility in gcompare"
        where
          x' = toConstr x
          y' = toConstr y
          repX = constrRep x'
          repY = constrRep y'

-- FIXME: I think there is an issue with the fold given a default branch:
-- we cannot always fold a branch in this case I think. Maybe we could do
-- something like include it in the outer case?
duplicateCase :: Map CmpExpr (AltCon, [CoreBndr]) -> CoreExpr -> CoreM CoreExpr
duplicateCase scruts = \case
  -- We have case split over this scrutinee if we enter this case. Thus, we can
  -- remove the case split by selecting the branch that was taken previously.
  -- We take care of the binders in the term to reference the outer case.
  Case scrut bind _ alts | Just (c, bs) <- Map.lookup (CmpExpr scrut) scruts -> do
    -- A matching alt should always be available.
    let Alt _ bs' rhs = fromJust $ matchingAlt alts c

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, the binder should be substituted by the scrutinee.
    let mapping = (bind, scrut) : zip bs' (Var <$> bs)

    -- Get the inscope variables
    let inscope = mkInScopeSet $ exprFreeVars rhs

    -- Make the substition using the mapping and perform the substitution
    let subst = extendIdSubstList (mkEmptySubst inscope) mapping

    -- Substitute the alts in the expression
    let expr = substExpr subst rhs

    -- Attempt to fold more cases in the new expression.
    duplicateCase scruts expr

  -- We have not case split over this scrutinee before, thus we add it to the
  -- map and continue. We do not have to traverse the scrutinee itself for the
  -- fold in this scenario, as the case distribute pass makes sure that no
  -- scrutinee can contain a case.
  Case scrut bind ty alts -> do
    let withAlt (Alt c bs rhs) = do
          let scruts' = Map.insert (CmpExpr scrut) (c, bs) scruts
          Alt c bs <$> duplicateCase scruts' rhs

    Case scrut bind ty <$> mapM withAlt alts

  e -> gmapM (mkM $ duplicateCase scruts) e
