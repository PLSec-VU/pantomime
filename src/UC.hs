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
import Data.List (foldl', find)
import Data.Maybe (fromJust)

import Data.Data
import Generics.SYB hiding (empty)

import Control.Applicative ((<|>), empty)
import Control.Monad ((>=>))
-- import Control.Monad.Trans.Maybe

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
  -- putMsgS $ "Non-recursive binding named " ++ showSDoc dflags (ppr b)
  -- putMsg $ ppr e
  -- putMsgS "--------------------------------"
  e' <- transforms e
  let bndr' = NonRec x e'
  putMsg . ppr $ bndr'

  let cfg = initLintConfig dflags []
  let res = lintCoreBindings' cfg [bndr']
  putMsg . ppr $ res

  -- putMsgS $ gshow e'
  return bndr
printBind bndr = return bndr

type FixPass = (CoreExpr -> CoreM (Maybe CoreExpr))
type FixPass' = (CoreExpr -> Maybe CoreExpr)

transforms :: CoreExpr -> CoreM CoreExpr
transforms = fix fused -- >=> caseFold Map.empty 

fix :: FixPass -> CoreExpr -> CoreM CoreExpr
fix f = everywhereM $ mkM go
  where
    go e = f e >>= \case
      Just e' -> fix f e'
      Nothing -> return e

fuse :: [FixPass] -> FixPass
fuse = foldl' fuse' (\_ -> return Nothing)

fuse' :: FixPass -> FixPass -> FixPass
fuse' p p' e = p e >>= \case
  Just e' -> return $ Just e'
  Nothing -> p' e

fused :: FixPass
fused = fuse
  [ return . inlineLet
  -- , return . betaReduce
  , return . caseDistribute
  -- , return . caseReduce
  -- , return . redundantCase
  ]

-- | Beta reduction (but with a let)
inlineLet :: FixPass'
inlineLet = \case
  Let (NonRec bind expr) body -> Just $ substitute body bind expr
  _ -> Nothing

-- | Beta reduction
betaReduce :: FixPass'
betaReduce = \case
  App (Lam bind body) arg -> Just $ substitute body bind arg
  _ -> Nothing

-- | substitute e1 x e2 = e1[x:=e2]
substitute :: CoreExpr -> CoreBndr -> CoreExpr -> CoreExpr
substitute body bind expr = do
  let inScope = mkInScopeSet $ exprFreeVars body
  let subst = extendIdSubst (mkEmptySubst inScope) bind expr
  let body' = substExpr subst body
  body'

-- | Reduces a case expression if the spine of the scrutinee is a constructor.
caseReduce :: FixPass'
caseReduce = \case
  Case scrut bind _ alts -> do
    -- Get the spine if it is a constructor
    (ac, es) <- spine scrut

    -- Get the alt matching this spine
    Alt _ bs rhs <- matchingAlt alts ac

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, the binder should be substituted by the scrutinee.
    let mapping = (bind, scrut) : zip bs es

    -- Make the substition using the mapping and perform the substitution
    let subst = extendIdSubstList (mkEmptySubst $ mkInScopeSet $ exprFreeVars rhs) mapping
    let expr = substExpr subst rhs
    return expr
  _ -> Nothing
  where
    -- | Get the constructor spine (if available) of this expression with all
    -- the arguments that are applied to it.
    spine :: CoreExpr -> Maybe (AltCon, [CoreExpr])
    spine = \case
      App fun arg -> second (arg :) <$> spine fun
      Var v | isDataConWorkId v -> return (DataAlt (idDataCon v), [])
      Lit l -> return (LitAlt l, [])
      _ -> Nothing

-- | Distrubte expressions over a case. This pushes case expressions towards the
-- root of the expression.
caseDistribute :: FixPass'
caseDistribute = \case
  -- Nested case
  -- Case cas@(Case {}) bind ty alts -> distribute (\e -> Case e bind ty alts) cas

  -- Inline function into case
  App fun@(Case {}) arg -> distribute (`App` arg) fun

  -- Inline argument into case
  App fun arg@(Case {}) -> distribute (App fun) arg

  _ -> empty
  where
    distribute f = \case
      Case scrut bind _ alts -> do
        let distribute' (Alt c bs e) = Alt c bs (f e)
        let alts' = distribute' <$> alts
        let ty' = coreAltsType alts'
        let expr = Case scrut bind ty' alts'
        return expr
      _ -> empty

-- TODO: Implement redundant case pass.
redundantCase :: FixPass'
redundantCase = const Nothing

matchingAlt :: [Alt a] -> AltCon -> Maybe (Alt a)
matchingAlt alts ac = matching <|> default'
  where
    matching = find (\(Alt con _ _) -> con == ac) alts
    default' = find (\(Alt con _ _) -> con == DEFAULT) alts

newtype CmpExpr = CmpExpr CoreExpr
  deriving (Data, Typeable)

instance Outputable CmpExpr where
  ppr (CmpExpr e) = ppr e

instance Eq CmpExpr where
  (==) = eq'
    where
      eq' :: GenericQ (GenericQ Bool)
      eq' x y
        | toConstr x == toConstr y = case (cast x, cast y) of
            (Just (v1 :: Var), Just (v2 :: Var)) -> v1 == v2
            _ -> and (gzipWithQ eq' x y)
        | otherwise = False

instance Ord CmpExpr where
  compare = gcompare'
    where
      gcompare' :: (Data a, Data b) => a -> b -> Ordering
      gcompare' x y = case (cast x, cast y) of
        (Just (v1 :: Var), Just (v2 :: Var)) -> compare v1 v2
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

-- FIXME: I think there is an issue with the fold in the default branch:
-- we cannot always fold a branch in this case I think. Maybe we could do
-- something like include it in the outer case?
caseFold :: Map CmpExpr (AltCon, [CoreBndr]) -> CoreExpr -> CoreM CoreExpr
caseFold scruts = \case
  -- We have case split over this scrutinee if we enter this case. Thus, we can
  -- remove the case split by selecting the branch that was taken previously.
  -- We take care of the binders in the term to reference the outer case.
  Case scrut bind _ alts | Just (c, bs) <- Map.lookup (CmpExpr scrut) scruts -> do
    -- A matching alt should always be available.
    let Alt _ bs' rhs = fromJust $ matchingAlt alts c

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, the binder should be substituted by the scrutinee.
    let mapping = (bind, scrut) : zip bs' (Var <$> bs)

    -- Make the substition using the mapping and perform the substitution
    let subst = extendIdSubstList (mkEmptySubst $ mkInScopeSet $ exprFreeVars rhs) mapping

    -- Substitute the alts in the expression
    let expr = substExpr subst rhs

    -- Attempt to fold more cases in the new expression.
    caseFold scruts expr

  -- We have not case split over this scrutinee before, thus we add it to the
  -- map and continue. We do not have to traverse the scrutinee itself for the
  -- fold in this scenario, as the case distribute pass makes sure that no
  -- scrutinee can contain a case.
  Case scrut bind ty alts -> do
    let withAlt (Alt c bs rhs) = do
          let scruts' = Map.insert (CmpExpr scrut) (c, bs) scruts
          Alt c bs <$> caseFold scruts' rhs

    Case scrut bind ty <$> mapM withAlt alts

  e -> gmapM (mkM $ caseFold scruts) e
