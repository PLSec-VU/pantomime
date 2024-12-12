module Lint
  ( panic
  , full
  , base
  , extra
  ) where

import GHC.Plugins hiding (panic)
import Data.Function ((&))
import Control.Monad (forM_, foldM)
import Control.Applicative ((<|>))

import GHC.Core.Lint (lintExpr)
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.Data.Bag (Bag, unitBag)

-- | Lint but panic on error.
panic
  :: HasCallStack
  => Monad m
  => HasDynFlags m
  => InScopeSet
  -> CoreExpr
  -> m ()
panic scope expr = full scope expr >>= \case
  Nothing -> pure ()
  Just err -> pprPanic "panicLint" $ hcat
    [ ppr expr
    , ppr scope
    , ppr err
    ]

-- | Perform both base and extra lints.
full
  :: Monad m
  => HasDynFlags m
  => InScopeSet
  -> CoreExpr
  -> m (Maybe (Bag SDoc))
full scope expr = do
  err <- base scope expr
  pure $ err <|> extra scope expr

-- | Perform GHC base lints.
base
  :: Monad m
  => HasDynFlags m
  => InScopeSet
  -> CoreExpr
  -> m (Maybe (Bag SDoc))
base _ (Type _) = pure Nothing
base _ (Coercion _) = pure Nothing
base (InScope vars) expr = do
  dflags <- getDynFlags
  let vars' = nonDetEltsUniqSet vars
  let cfg = initLintConfig dflags vars'
  pure $ lintExpr cfg expr

-- | Perform additional lints.
extra
  :: InScopeSet
  -> CoreExpr
  -> Maybe (Bag SDoc)
extra scope expr = lintExtra scope expr & \case
  Right _ -> Nothing
  Left err -> Just $ unitBag (ppr err)

-- | Extra linter errors.
data LintExtra
  = Shadow CoreBndr CoreBndr
  | NameMismatch CoreBndr CoreBndr
  | FreeVariable CoreBndr

instance Outputable LintExtra where
  ppr (Shadow old new) = hsep
    [ text "Variable"
    , ppr old
    , text "was shadowed by"
    , ppr new
    ]
  ppr (NameMismatch def occ) = hsep
    [ text "Defined variable"
    , ppr def
    , text "occurred with different name"
    , ppr occ
    ]
  ppr (FreeVariable var) = text "Free variable" <+> ppr var

-- | Lints extra properties.
--
-- This will additionally check whether no shadowing occurs, occurence names
-- do not match up, or free variables occur.
lintExtra
  :: InScopeSet
  -> CoreExpr
  -> Either LintExtra ()
lintExtra scope = \case
  Var var -> do
    case lookupInScope scope var of
      Just bndr | occName bndr == occName var -> pure ()
      Just bndr -> Left $ NameMismatch bndr var
      _ | isGlobalId var -> pure ()
      _ -> Left $ FreeVariable var

  -- TODO: Should we check the type?
  Type _ -> pure ()

  -- TODO: Should we check the coercion?
  Coercion _ -> pure ()

  Lit _ -> pure ()

  App fun arg -> do
    lintExtra scope fun
    lintExtra scope arg

  Tick _ expr -> do
    -- TODO: Should we check the tick?
    lintExtra scope expr

  Cast expr _ -> do
    lintExtra scope expr
    -- TODO: Should we check the coercion?

  Lam bndr body -> do
    scope' <- scope & lintBndr bndr
    lintExtra scope' body

  Let bind body -> do
    scope' <- scope & lintBind bind
    lintExtra scope' body

  Case scrut bndr _ alts -> do
    lintExtra scope scrut
    -- TODO: Should we check the type?

    scope' <- scope & lintBndr bndr

    forM_ alts $ \(Alt _ bndrs rhs) -> do
      scope'' <- scope' & lintBndrs bndrs
      lintExtra scope'' rhs
  where
    lintBndr bndr scope' = do
      case lookupInScope scope' bndr of
        Just old -> Left $ Shadow old bndr
        _ -> pure ()
      pure $ extendInScopeSet scope' bndr

    lintBndrs = flip $ foldM (flip lintBndr)

    lintBind (NonRec bndr expr) scope' = do
      lintExtra scope' expr
      lintBndr bndr scope'
    lintBind (Rec pairs) scope' = do
      let (bndrs, exprs) = unzip pairs
      scope'' <- lintBndrs bndrs scope'
      forM_ exprs $ lintExtra scope''
      pure scope''


