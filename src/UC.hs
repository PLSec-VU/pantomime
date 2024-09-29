{-# LANGUAGE ScopedTypeVariables #-}

module UC
  ( plugin
  , UC (..)
  , UCCompare (..)
  , UCNorm (..)
  , UCTactic (..)
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Lint
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
-- import GHC.Core.Map.Expr (eqCoreExpr)

import GHC.MonadCore
import Data.Maybe (catMaybes)

import Data.Data

import Control.Monad.Reader (ReaderT (..), reader)
import Control.Monad (forM, foldM)

import qualified Language.Haskell.TH.Syntax as TH

import qualified Projection
import Types
import Util
import Transform

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

-- TODO: Change printUCGenerated to printAnnotated, which should take a type
-- parameter.
install :: MonadCore m => [CommandLineOption] -> Pass m [CoreToDo]
install _ todo = return $ mconcat
  -- [ checkPasses
  [ normalizePasses
  -- , cmpPasses
  , inferPasses
  , todo
  ]
  where
    -- cmpPasses = [CoreDoPluginPass "compareNormalforms" compareNormalforms]

    -- checkPasses = [doCheck]

    withProxy proxy ls = (\f -> f proxy) <$> ls

    normalizePasses = withProxy (Proxy @(UCGenerated UCNorm))
      [ createUCBindsPass
      , normalizePass
      , printAndLintPass
      , removeUCBindsPass
      ]

    inferPasses = withProxy (Proxy @(UCGenerated (UC TH.Name)))
      [ createUCBindsPass
      , projectOutputPass
      , normalizePass
      , printAndLintPass
      , removeUCBindsPass
      ]
    -- inferPasses =
    --   [ CoreDoPluginPass "CreateInferenceBinds" createInferenceBinds
    --   , CoreDoPluginPass "ProjectOutput" projectOutput
    --   -- , inlineAllPass proxy
    --   -- , dedupCasesPass proxy
    --   -- , printAndLintPass proxy
    --   -- , CoreDoPluginPass "SplitExprs" splitExprs
    --   -- , CoreDoPluginPass "splitExpr" $ splitExprs proxy
    --   , normalizePass proxy'
    --   , printAndLintPass proxy
    --   -- , reorderCasesPass proxy
    --   -- , printAndLintPass proxy
    --   -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
    --   -- , CoreLiberateCase
    --   -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
    --   , CoreDoPluginPass "RemoveUCBinds" removeUCBinds
    --   ]

createUCBinds
  :: forall m a b. (Data a, Data b, MonadFail m, MonadCore m)
  => (a -> m b)
  -> Pass m ModGuts
createUCBinds f guts = do
  -- FIXME: We should check that there exists strictly one annotation per bind
  -- (and ideally that all of them are non-recursive).
  (_, anns) <- liftCore $ getFirstAnnotations @a deserializeWithData guts

  -- Runs the function on the given CoreBind, given that the CoreBind is
  -- non-recursive.
  let genBind :: CoreBind -> m (Maybe (b, CoreBind'))
      genBind = \case
        NonRec var expr | Just ann <- lookupUFM anns $ varName var -> do
          let name = "ucgenerated_" <> occNameString (occName var)
          var' <- freshGlobalVar name $ varType var
          ann' <- f ann
          let bind = Bind' var' expr
          return $ Just (ann', bind)
        _ -> return Nothing

  -- Get all generated bindings.
  gen <- catMaybes <$> mapM genBind (mg_binds guts)
  let annots = uncurry ucGenAnn <$> gen
  let binds = nonRec . snd <$> gen

  -- Return the guts with the additional binders.
  return guts
    { mg_binds = binds <> mg_binds guts
    , mg_anns = annots <> mg_anns guts
    }

-- | Run the given pass on all binders that have the given annotation.
annBindsPass
  :: forall m a. (Data a, MonadCore m)
  => (a -> Pass m CoreBind')
  -> Pass m ModGuts
annBindsPass pass guts = do
  (_, anns) <- liftCore $ getFirstAnnotations @a deserializeWithData guts

  binds <- forM (mg_binds guts) $ \case
    NonRec x e | Just ann <- lookupUFM anns $ varName x -> do
      nonRec <$> pass ann (Bind' x e)
    b -> return b

  return guts { mg_binds = binds }

annBindsPassWithGuts 
  :: MonadCore m
  => Data a
  => (a -> Pass (ReaderT ModGuts m) CoreBind')
  -> Pass m ModGuts
annBindsPassWithGuts f mods = annBindsPass f' mods
  where
    f' a = flip runReaderT mods . f a

createUCBindsPass
  :: forall a. Data a
  => Proxy (UCGenerated a)
  -> CoreToDo
createUCBindsPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'createUCBindsPass
    pass = createUCBinds $ return @_ @a

removeUCBindsPass :: Proxy (UCGenerated a) -> CoreToDo
removeUCBindsPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'removeUCBindsPass
    pass = removeUCBinds

printAndLintPass
  :: forall a. Data a
  => Proxy a
  -> CoreToDo
printAndLintPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'printAndLintPass
    pass = annBindsPassWithGuts $ \(_ :: a) -> printAndLint

normalizePass
  :: forall a. Data a
  => Proxy a
  -> CoreToDo
normalizePass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'normalizePass
    pass = annBindsPassWithGuts $ \(_ :: a) -> bindPass normalize

projectOutputPass :: proxy (UCGenerated (UC TH.Name)) -> CoreToDo
projectOutputPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'projectOutputPass
    pass = projectOutput

-- inlineAllPass
--   :: forall a proxy. Data a
--   => proxy a
--   -> CoreToDo
-- inlineAllPass _ = CoreDoPluginPass name pass
--   where
--     name = TH.nameBase 'inlineAllPass
--     pass = annBindsPass $ \(_ :: a) -> inlineAll

-- dedupCasesPass
--   :: forall a proxy. Data a
--   => proxy a
--   -> CoreToDo
-- dedupCasesPass _ = CoreDoPluginPass name pass
--   where
--     name = TH.nameBase 'dedupCasesPass
--     pass = annBindsPass $ \(_ :: a) -> dedupCases

-- reorderCasesPass
--   :: forall a proxy. Data a
--   => proxy a
--   -> CoreToDo
-- reorderCasesPass _ = CoreDoPluginPass name pass
--   where
--     name = TH.nameBase 'reorderCasesPass
--     pass = annBindsPass $ \(_ :: a) -> reorderCases

-- encloseStatePass
--   :: forall a proxy. Data a
--   => proxy a
--   -> CoreToDo
-- encloseStatePass _ = CoreDoPluginPass name pass
--   where
--     name = TH.nameBase 'encloseStatePass
--     pass = annBindsPass $ \(_ :: a) -> encloseState

-- doCheck :: CoreToDo
-- doCheck = CoreDoPluginPass name pass
--   where
--     name = TH.nameBase 'doCheck
--     pass guts = annBindsPass (doCheck' $ mg_binds guts) guts

-- doCheck' :: (MonadCore m, MonadFail m) => CoreProgram -> UCCheck TH.Name -> Pass m CoreBind'
-- doCheck' prog uc bind = do
--   let resolve = resolveTH' prog

--   -- Fetch projection functions
--   sproj <- resolve 'Projection.sproj
--   sproj' <- resolve 'Projection.sproj'
--   iproj <- resolve 'Projection.iproj
--   oproj <- resolve 'Projection.oproj

--   obs <- resolve $ ch_obs uc
--   impl <- resolve $ ch_impl uc

--   leak <- resolve $ ch_leak uc
--   sim <- resolve $ ch_sim uc

--   ignfun <- resolve $ ch_ignfun uc
--   ignsim <- resolve $ ch_ignsim uc

--   let show' :: Outputable o => o -> String
--       show' = showSDocUnsafe . ppr

--   let app (Bind' lvar lexpr) (Bind' rvar rexpr) = do
--         let showvar var = show' var <> " :: " <> show' (varType var)
--         expr <- polyApp lexpr rexpr
--           ??= "Incompatible application:\n  " <> showvar lvar <> "\n  " <> showvar rvar
--         var <- freshLocalVar "fresh" $ exprType expr
--         return $ Bind' var expr

--   let app' fun args = do
--         Bind' var expr <- foldM app fun args
--         return $ Bind' var (occurAnalyseExpr expr)

--   let normalize' = bindPass normalize

--   let cmp errmsg lhs rhs = do
--         lhs'@(Bind' lvar lexp) <- normalize' lhs
--         rhs'@(Bind' rvar rexp) <- normalize' rhs
--         unless (lexp `eqCoreExpr` rexp) $ do
--           dbg lhs'
--           dbg rhs'
--           fail $ errmsg <> ": " <> show' lvar <> " =/= " <> show' rvar

--   oprojected <- app' oproj [obs, impl]
--   sprojected <- app' sproj [ignfun, oprojected]
--   sprojected' <- app' sproj' [ignfun, ignsim]

--   cmp "State projection not equal" sprojected sprojected'

--   iprojected <- app' iproj [leak, sim]

--   cmp "Input projection not equal" sprojected' iprojected

--   return bind

-- projectOutputPass :: CoreToDo
-- projectOutputPass = CoreDoPluginPass name pass
--   where
--     name = TH.nameBase 'projectOutputPass
--     pass = ucBindsPass projectOutput

printAndLint :: MonadCore m => MonadMod m => Pass m CoreBind'
printAndLint bind = do
  dflags <- liftCore getDynFlags
  let cfg = initLintConfig dflags []
  prog <- reader mg_binds
  let res = lintCoreBindings' cfg prog
  dbg bind
  dbg res
  return bind

-- | Project the output of all generated UC binders, according to the
-- observation function in the annotation.
projectOutput :: MonadFail m => MonadCore m => Pass m ModGuts
projectOutput guts = flip annBindsPass guts $ \(UCGenerated uc) (Bind' var expr) -> do
  let prog = mg_binds guts

  Bind' _ oproj <- resolveTH' prog 'Projection.oproj

  Bind' _ obs <- resolveTH' prog (observable uc)

  expr' <- occurAnalyseExpr <$> foldM polyApp oproj [obs, expr]
    ??= "Incompatible types on observation/implementation pair"

  let var' = setVarType var $ exprType expr'
  return $ Bind' var' expr'

-- compareNormalforms :: MonadFail m => MonadCore m => Pass m ModGuts
-- compareNormalforms guts = flip annBindsPass guts $ \(UCCompare other) bind -> do
--   let prog = mg_binds guts

--   let normalize' = bindPass normalize

--   other' <- resolveTH' prog other

--   lhs <- normalize' other'
--   rhs <- normalize' bind
--   let cmp (Bind' _ l) (Bind' _ r) = eqCoreExpr l r
--   unless (lhs `cmp` rhs) $ do
--     dbg other'
--     dbg lhs
--     dbg bind
--     dbg rhs
--     fail "Expressions were non-equal"
--   return bind

-- splitExprs
--   :: forall a m proxy. Data a
--   => MonadCore m
--   => proxy a
--   -> Pass m ModGuts
-- splitExprs _ = annBindsPass $ \(_ :: a) (Bind' x e) -> do
--   let fused = fuse
--         [ redundantCase
--         , caseFactor
--         ]

--   e' <- occurAnalyseExpr <$> fix fused e
--   return $ Bind' x e'

-- TODO: Implement this!
removeUCBinds :: MonadCore m => Pass m ModGuts
removeUCBinds guts = do
  return guts
