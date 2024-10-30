module Fusion
  ( fuse
  , (<|-|>)
  , fix
  , fixWithEnv
  , singlePass
  ) where

import GHC.Plugins hiding (empty, substExpr, (<>))
import GHC.MonadCore
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.Core.Lint (lintExpr)

import Data.List (foldl')
import Data.Generics hiding (empty)
import Data.IORef

import Control.Monad (forM, guard)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Reader (MonadReader, reader, ReaderT (runReaderT))
import Control.Applicative (Alternative (..), empty)

import Types

-- | Fuse all the given passes; the first succesful pass wil return its result.
fuse :: Alternative m => [Pass m a] -> Pass m a
fuse = foldl' (<|-|>) $ const empty

-- | Fuses two passes; the first succesful pass will return its result.
(<|-|>) :: Alternative m => Pass m a -> Pass m a -> Pass m a
(<|-|>) p p' e = p e <|> p' e

-- | Fixpoint pass environment.
--
-- Passes may use this exposed environment to perform operations.
data Env = Env
  { envModGuts :: ModGuts
  , envInScopeSet :: InScopeSet
  , envOrderedDecl :: [CoreBndr]
  , envCaseBndrs :: VarSet
  }

instance HasModGuts Env where
  modGuts = envModGuts

instance HasInScopeSet Env where
  inScopeSet = envInScopeSet

instance HasOrderedDecl Env where
  orderedDecl = envOrderedDecl

instance HasCaseBndrs Env where
  caseBndrs = envCaseBndrs

-- | Initial environment.
initEnv :: MonadReader r m => HasModGuts r => m Env
initEnv = do
  guts <- reader modGuts
  let binds = mg_binds guts
  pure Env
    { envModGuts = guts
    , envInScopeSet = mkInScopeSetBndrs binds
    , envOrderedDecl = foldBindersOfBindsStrict (flip (:)) [] binds
    , envCaseBndrs = mempty
    }

-- | Extend the environment with a variable.
extendEnv :: Env -> Var -> Env
extendEnv env var = env
  { envInScopeSet = extendInScopeSet (inScopeSet env) var
  , envOrderedDecl = var : envOrderedDecl env
  , envCaseBndrs = delVarSet (envCaseBndrs env) var
  }

extendEnvCaseBndr :: Env -> Var -> Env
extendEnvCaseBndr env var = (extendEnv env var)
  { envCaseBndrs = extendVarSet (envCaseBndrs env) var
  }

-- | Extend the environment with multiple variables.
extendEnvList :: Env -> [Var] -> Env
extendEnvList = foldr $ flip extendEnv

-- | Extend the environment with a core binder.
extendEnvBind :: Env -> CoreBind -> Env
extendEnvBind = foldBindersOfBindStrict extendEnv

lintExpr'' :: MonadCore m => Env -> CoreExpr -> m ()
lintExpr'' env expr = do
  dflags <- liftCore getDynFlags
  let vars = nonDetStrictFoldVarSet (:) [] . getInScopeVars . inScopeSet $ env
  let cfg = initLintConfig dflags vars
  case lintExpr cfg expr of
    Just v -> do
      dbg' "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
      dbg expr
      dbg v
      error "Stopping! Lint error in fix"
    Nothing -> pure ()

fix :: Monad m => Pass (MaybeT m) a -> Pass m a
fix pass x = runMaybeT (pass x) >>= \case
  Just x' -> fix pass x'
  Nothing -> pure x

-- | Run the pass until we reach a fixed point.
--
-- This will continuously invoke the pass in a bottom-up manner. Additionally,
-- it will expose additional environment for usage in the pass via the reader
-- monad.
fixWithEnv
  :: MonadReader r m
  => HasModGuts r
  => Pass (ReaderT Env (MaybeT m)) CoreExpr
  -> Pass m CoreExpr
fixWithEnv pass e = do
  let go env expr = do
        expr' <- case expr of
          Lam bndr body -> do
            let env' = extendEnv env bndr
            body' <- go env' body
            pure $ Lam bndr body'

          Let bind body -> do
            let env' = extendEnvBind env bind
            body' <- go env' body
            pure $ Let bind body'

          Case scrut bndr ty alts -> do
            scrut' <- go env scrut

            let env' = extendEnvCaseBndr env bndr

            alts' <- forM alts $ \(Alt con bndrs rhs) -> do
              let env'' = extendEnvList env' bndrs
              rhs' <- go env'' rhs
              pure $ Alt con bndrs rhs'

            pure $ Case scrut' bndr ty alts'

          -- Remaining expressions don't introduce binders, so we map generically.
          _ -> gmapM (mkM $ go env) expr

        -- Run the pass, if it transforms the expression we again.
        let runPass = runMaybeT . flip runReaderT env . pass
        runPass expr' >>= \case
          Just expr'' -> go env expr''
          Nothing -> pure expr'
        
  env <- initEnv
  go env e

singlePass
  :: Alternative m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => Pass (ReaderT Env m) CoreExpr
  -> Pass m CoreExpr
singlePass pass e = do
  let go env expr = do
        -- Bottom up recursion, extending the environment with variables when
        -- applicable.
        let runPass = flip runReaderT env . pass

        let inner = case expr of
              Lam bndr body -> do
                let env' = extendEnv env bndr
                body' <- go env' body
                pure $ Lam bndr body'

              Let bind body -> do
                let env' = extendEnvBind env bind
                body' <- go env' body
                pure $ Let bind body'

              Case scrut bndr ty alts -> do
                let adjustScrut = do
                      scrut' <- go env scrut
                      pure $ Case scrut' bndr ty alts

                let adjustAlts = do
                      ref <- liftCore . liftIO $ newIORef False
                      let env' = extendEnvCaseBndr env bndr
                      alts' <- forM alts $ \(Alt con bndrs rhs) -> do
                        let env'' = extendEnvList env' bndrs
                        let test = do
                              changed <- liftCore . liftIO $ readIORef ref
                              if changed
                                then pure rhs
                                else do
                                  rhs' <- go env'' rhs
                                  liftCore . liftIO $ writeIORef ref True
                                  pure rhs'
                        rhs' <- test <|> pure rhs
                        pure $ Alt con bndrs rhs'

                      changed <- liftCore . liftIO $ readIORef ref
                      guard changed

                      pure $ Case scrut bndr ty alts'

                adjustScrut <|> adjustAlts

              Var _ -> runPass expr
              Lit _ -> runPass expr
              Type _ -> runPass expr
              Coercion _ -> runPass expr

              App fun arg -> (flip App arg <$> go env fun) <|> (App fun <$> go env arg)
              Cast body coerce -> flip Cast coerce <$> go env body
              Tick tick body -> Tick tick <$> go env body

              -- Remaining expressions don't introduce binders, so we map generically.
              -- _ -> gmapMo (mkM $ go env) expr

        -- Run the inner change, if there is no modification, the pass on the
        -- current expression.
        runPass expr <|> inner
        -- inner <|> runPass expr

  env <- initEnv

  e' <- go env e
  lintExpr'' env e'
  pure e'

