{-# LANGUAGE OverloadedStrings #-}
-- TODO: I want to remove many of these pragmas, also for the other files. Most
-- of them should just be included in the top-level flags. There also seems to
-- be a lot of obsolete stuff. Perhaps its good to first find out which flags
-- are actually used. I actually removed most of them here, but there's still
-- way too many in other files. Isn't there an 'obsolete pragma warning' or
-- something in GHC?

-- TODO: I feel like the pantomime dependencies that are used solely by the
-- final solver should go under Pantomime.Solve.X (e.g. Pantomime.Solve.Value).
-- Right now, the hierarchy is a bit too flat, which makes the project structure
-- a lot less clear. Alternatively, we can use Pantomime.Symbolic.X

module Pantomime.Solve
  ( NonEq (..)
  , checkValid
  , exprSymEq
  ) where

import GHC.Plugins
import GHC.Platform (PlatformWordSize (..), Platform (..))
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Tc.Utils.TcType (eqType, tcSplitSigmaTy)

import Grisette (LogicalOp (..), ModelOps (..), IfViewResult (..), UnionView (..), SymBranching (..), onUnion, EvalSym (..))

import Control.Monad (unless)

import Data.List (intersperse)

import Language.Haskell.TH qualified as TH

import Pantomime.WordSize
import Pantomime.Evaluate
import Pantomime.Environment
import Pantomime.Value
import Pantomime.Concrete (Concrete, concretise, concretise2)
import Pantomime.Runtime
import Pantomime.MonadEval
import Pantomime.Expr qualified as Pantomime
import Pantomime.Symbolise qualified as Pantomime
import Pantomime.Subst qualified as Pantomime
import Pantomime.Fresh qualified as Pantomime
import Pantomime.Primitive.GHC qualified as Primitive

-- TODO: These modules should just get their own package such that a user can
-- just provide the interpretations they require for the code!
import Pantomime.Base
import Pantomime.Clash

import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.DynFlags
import Effectful.Grisette.Fresh
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.GHC.External
import Effectful.Grisette.Solver
import Effectful.Provider
import Effectful.Exception (ErrorCall (..), throwIO)
import Effectful.Dispatch.Static (unsafeEff_)
import Data.Traversable (forM)
import Data.Foldable (for_)
import Control.Monad.Except (runExceptT)
import Pantomime.Result (handle, ok)
-- import Pantomime.Primitive.Interpret (interpPlus)

checkValid
  :: forall es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error SolverError :> es
  => Context Reader CoreProgram :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => HasFamInstEnvs :> es
  => Provider_ Solver () :> es
  => CoreExpr
  -> Eff es ()
checkValid expr = do
  let dbg :: forall o es'. Outputable o => o -> Eff es' ()
      dbg = unsafeEff_ . putStrLn . showSDocUnsafe . ppr

  program <- get @CoreProgram

  reifiedIntN <- Primitive.reifiedIntN
  reifiedBase <- Primitive.reifiedBase
  -- dbg $ getUnique plusvar
  -- dbg $ exprType lhs
  let subst = do
        subst' <- Pantomime.extendSubstMany Pantomime.mkEmptySubst reifiedIntN
        subst'' <- Pantomime.extendSubstMany subst' reifiedBase
        Pantomime.symboliseBindMany subst'' program

  subst' <- case handle subst of
    -- TODO: Properly propagate error!
    Left (_cs, ()) -> undefined
    Right value -> pure $ ok value

  famInst <- getFamInstEnvs
  primTys <- Primitive.getTypes
  let ty = exprType expr

  let (args, _scope) = Pantomime.freshArgs famInst primTys ty emptyInScopeSet

  let result = do
        fun <- Pantomime.symbolise subst' expr
        Pantomime.mkApps fun (fmap snd args)
          -- fun >>= flip Pantomime.mkApps (fmap snd args)

  -- let symbolic = do
  --       -- subst' <- Pantomime.extendSubst subst plusvar plusexpr
  --       fun <- Pantomime.symbolise subst expr
  --       Pantomime.saturate famInst primTys fun

  -- let evalBool = symbolic >>= Pantomime.exprToBool . fst
  -- let binds = sequence $ snd <$> symbolic
        -- (saturated, _binds) <- Pantomime.saturate famInst primTys fun
        -- Pantomime.exprToBool saturated

  let boolResult = result >>= Pantomime.exprToBool

  -- TODO: I should make a better interface to strip errors! This code is really
  -- horrible anyway, so I should clean it up...
  evalBool <- forUnion (runExceptT $ Pantomime.runEval boolResult) \case
    Left (Left _err) -> do
      -- dbg $ "UNKNOWN ERROR :(" $+$ text (prettyCallStack trace)
      undefined
    Left (Right variant) -> pure $ Left variant
    Right value -> pure $ Right value

  let eq = flip onUnion evalBool \case
        Left Pantomime.Unreachable -> true
        Left Pantomime.UB -> false
        Left Pantomime.Raise {} -> false
        Right value -> value

  solution <- provide_ @Solver $ solve (symNot eq)

  dbg result
  -- dbg $ Pantomime.pprEval id (const $ text . show) result

  -- TODO: Do we not have to assert that the input is never Invalid?
  -- I.e. if we want to prove equivalence between (assuming inputs cannot be
  -- bottom):
  --
  -- ex1 :: Void -> Int
  -- ex1 _ = 0
  --
  -- ex2 :: Void -> Int
  -- ex2 _ = 1
  --
  -- Then we need to pass in the constraint that Void only contains Invalid
  -- as a value.
  case solution of
    Satisfiable model -> do
      dbg @SDoc $ text (show model)
      for_ args \(bndr, arg) -> do
        let arg' = evalSym True model arg
        dbg $ vcat
          [ "==================="
          , ppr bndr <+> "::" <+> ppr (varType bndr)
          , Pantomime.pprArg id arg'
          ]
      -- let args' = evalSym true model . snd <$> args
      -- let counterExample = evalSym true model result
      -- dbg $ Pantomime.pprArg id <$> args'
      -- dbg $ Pantomime.pprArg id counterExample

      -- dbg $ Pantomime.pprEval id (const $ text . show) counterExample
      error "Expression was **not** valid!"
      -- let concretise' = runEvalErr . concretise model
      -- bndrs' <- forM bndrs concretise'
      -- lres' <- concretise' lres
      -- rres' <- concretise' rres
      -- throwError_ $ Counterexample bndrs' lres' rres'
    Unsatisfiable -> do
      error "Expression was valid!"
      -- conc <- runEvalErr $ concretise2 emptyModel lres
      -- unsafeEff_ . print . showSDocUnsafe . ppr $ conc
      -- pure ()
    -- FIXME: I don't think this is always true. Especially so w.r.t. allowing
    -- user define Opaque types. Also not sure about some of the floating point
    -- stuff for example.
    Unknown -> throwIO $ ErrorCall "checks are in decidable fragment"

forUnion
  :: UnionView t
  => Applicative f
  => t a
  -> (a -> f b)
  -> f (t b)
forUnion = flip traverseUnion

traverseUnion
  :: UnionView t
  => Applicative f
  => (a -> f b)
  -> t a
  -> f (t b)
traverseUnion f m = if
  | Just x <- singleView m -> pure <$> f x
  | Just (IfViewResult cond tr fl) <- ifView m -> do
    mrgIfPropagatedStrategy cond <$> traverseUnion f tr <*> traverseUnion f fl
  -- TODO: This is aweful. Shouldn't Grisette just change the interface on
  -- this or something?... Note, we cannot use 'Single' and 'If' pattern
  -- as we cannot introduce a mergeable constraint on the values of the
  -- Union.
  | otherwise -> error "BUG: union should always be either 'Single' or 'If'"

-- TODO: We really want to remove this thing once we get rid of MonadEval in
-- the entire codebase. This return is a horrible overapproximation!
data NonEq
  -- TODO: It would be nice if the counterexample also included the final
  -- result. Even if just for checking whether the output is actually correct!
  = Counterexample [Concrete] Concrete Concrete
  | EvalError EvalError

instance Outputable NonEq where
  ppr = \case
    Counterexample bndrs lhs rhs -> do
      -- Vertically concatenate using ($+$).
      let vcat' = foldl' @[] ($+$) empty

      -- Vertically separate with newlines in between.
      let vsep' = vcat' . intersperse ""

      -- Hang that always aligns vertically.
      let hang' d1 n d2 = vcat' [d1, nest n d2]

      -- The actual pretty print.
      vsep'
        [ hang' "Diverging results given the following arguments" 2 do
          vsep' $ fmap ppr bndrs
        , hang' "Result left-hand side" 2 do
          ppr lhs
        , hang' "Result right-hand side" 2 do
          ppr rhs
        ]

    EvalError err -> text "eval-error:" <+> ppr err

exprSymEq
  :: forall es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error SolverError :> es
  => Context Reader CoreProgram :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => HasInstEnvs :> es
  => HasFamInstEnvs :> es
  => Provider_ Solver () :> es
  => HasDynFlagsE :> es
  => CoreExpr
  -> CoreExpr
  -> Eff es (Either NonEq ())
exprSymEq lhs rhs = do
  -- Get the target platform word size.
  dflags <- getDynFlags
  let pwsize = platformWordSize $ targetPlatform dflags

  -- We run the comparison with the word size of the target platform.
  case pwsize of
    PW4 -> exprSymEq' @PW4 lhs rhs
    PW8 -> exprSymEq' @PW8 lhs rhs

exprSymEq'
  :: forall ws es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error SolverError :> es
  => Context Reader CoreProgram :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => HasInstEnvs :> es
  => HasFamInstEnvs :> es
  => Provider_ Solver () :> es
  => KnownWordSize ws
  => CoreExpr
  -> CoreExpr
  -> Eff es (Either NonEq ())
exprSymEq' lhs rhs = runErrorNoCallStack @NonEq $ runFresh "fresh" do
  -- let dbg :: forall o es'. Outputable o => o -> Eff es' ()
  --     dbg = unsafeEff_ . putStrLn . showSDocUnsafe . ppr

  -- let dbg' :: forall es'. String -> Eff es' ()
  --     dbg' = unsafeEff_ . putStrLn

  -- let tr :: Pantomime.Expr S = Pantomime.Expr . pure $ Pantomime.Type boolTy
  -- let fl :: Pantomime.Expr S = Pantomime.Expr . pure $ Pantomime.Type intTy
  -- let tr :: Pantomime.Expr S = Pantomime.Expr . pure $ Pantomime.Lit (Pantomime.Int $ Pantomime.SomeBV @32 8)
  -- let fl :: Pantomime.Expr S = Pantomime.Expr . pure $ Pantomime.Lit (Pantomime.Int $ Pantomime.SomeBV @32 8)
  -- let e = mrgIte "a" tr fl

  -- famInst <- getFamInstEnvs
  -- primTys <- Primitive.getTypes
  -- program <- get @CoreProgram

  -- reifiedIntN <- Primitive.reifiedIntN
  -- reifiedBase <- Primitive.reifiedBase
  -- -- dbg $ getUnique plusvar
  -- -- dbg $ exprType lhs

  -- let expr' = do
  --       subst <- Pantomime.extendSubstMany Pantomime.mkEmptySubst reifiedIntN
  --       subst' <- Pantomime.extendSubstMany subst reifiedBase

  --       subst'' <- Pantomime.symboliseBindMany subst' program
  --       -- subst' <- Pantomime.extendSubst subst plusvar plusexpr
  --       fun <- Pantomime.symbolise subst'' lhs
  --       (saturated, _binds) <- Pantomime.saturate famInst primTys fun
  --       pure saturated
  --       -- let arg = pure $ Pantomime.mkLit (Pantomime.mkDataCon @64 $ trueDataCon)
  --       -- Pantomime.mkApp fun arg
  -- -- (result, args) <- Pantomime.saturateLam @(WordBits ws) fun
  -- dbg $ Pantomime.pprArg id expr'
  -- dbg doc
  -- dbg @SDoc "================"
  -- for_ args \(_, arg) -> do
  --   expr <- arg
  --   doc' <- Pantomime.pprExpr id expr
  --   dbg doc'
  -- result <- runError @() $ translate Pantomime.emptySubst lhs
  -- case result of
  --   Right expr -> dbg expr
  --   Left (stack, err) -> do
  --     dbg' "error!"
  --     dbg' $ prettyCallStack stack
  --     dbg err

  _ <- throwError_ $ EvalError UnboundVariable
  -- _ <- error "DONE!"

  let lty = exprType lhs
  let rty = exprType rhs
  unless (lty `eqType` rty) do
    throwError_ $ EvalError IllTyped

  -- TODO: I really would like to get rid of this. Or actually, just to get rid
  -- of the whole eval error thing as a whole.
  let runEvalErr = runErrorNoCallStackWith $ throwError_ . EvalError

  (bndrs, lres, rres, eq) <- runEvalErr do
    bndrs <- symbolicBndrs $ exprType lhs

    base <- baseValues
    clash <- clashInterp
    env <- extendManyEnv emptyEnv $ base ++ clash

    prog <- get @CoreProgram
    let env' = extendLocalEnv env prog

    let saturate expr = do
          value <- evaluate env' expr
          applyValues @_ @ws value bndrs

    lresult <- saturate lhs
    rresult <- saturate rhs
    eq <- weakEq lresult rresult
    pure (bndrs, lresult, rresult, eq)

  -- TODO: Do we not have to assert that the input is never Invalid?
  -- I.e. if we want to prove equivalence between (assuming inputs cannot be
  -- bottom):
  --
  -- ex1 :: Void -> Int
  -- ex1 _ = 0
  --
  -- ex2 :: Void -> Int
  -- ex2 _ = 1
  --
  -- Then we need to pass in the constraint that Void only contains Invalid
  -- as a value.
  result <- provide_ @Solver $ solve (symNot eq)

  case result of
    Satisfiable model -> do
      let concretise' = runEvalErr . concretise model
      bndrs' <- forM bndrs concretise'
      lres' <- concretise' lres
      rres' <- concretise' rres
      throwError_ $ Counterexample bndrs' lres' rres'
    Unsatisfiable -> do
      conc <- runEvalErr $ concretise2 emptyModel lres
      unsafeEff_ . print . showSDocUnsafe . ppr $ conc
      pure ()
    -- FIXME: I don't think this is always true. Especially so w.r.t. allowing
    -- user define Opaque types. Also not sure about some of the floating point
    -- stuff for example.
    Unknown -> throwIO $ ErrorCall "checks are in decidable fragment"

-- TODO: We have a function to create a fresh typed value now, together with
-- types attached to function values. We should be able to saturate a value
-- without being given its type separately.
symbolicBndrs
  :: forall ws es
   . Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Fresh :> es
  => HasFamInstEnvs :> es
  => KnownWordSize ws
  => Type
  -> Eff es [Value (Eff es) ws]
symbolicBndrs ty = do
  ty' <- case tcSplitSigmaTy ty of
    ([], [], ty') -> pure ty'
    -- TODO: Support polymorphism.
    -- For now, we don't support polymorphism or dictionaries at the top level.
    -- Do we really not at this point? I'll have to verify it!
    _ -> throwError_ UnsupportedExpr

  let (argTys, _) = splitFunTys ty'

  forM argTys \argTy -> do
    -- Type the symbolic variable according to the argument type.
    let argTy' = scaledThing argTy
    evalFresh (argTy', Right @RuntimeError ())
