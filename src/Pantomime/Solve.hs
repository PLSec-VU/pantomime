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
  , exprSymEq
  ) where

import GHC.Plugins
import GHC.Platform (PlatformWordSize (..), Platform (..))
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Tc.Utils.TcType (eqType, tcSplitSigmaTy)

import Grisette (LogicalOp (..))

import Control.Monad (forM, unless)

import Data.List (intersperse)

import Language.Haskell.TH qualified as TH

import Pantomime.WordSize
import Pantomime.Evaluate
import Pantomime.Environment
import Pantomime.Value
import Pantomime.Concrete (Concrete, concretise)
import Pantomime.Runtime
import Pantomime.MonadEval

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
  => Context Reader CoreProgram :> es
  => HasThings :> es
  => THNameToGHCName :> es
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
  => Context Reader CoreProgram :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => HasFamInstEnvs :> es
  => Provider_ Solver () :> es
  => KnownWordSize ws
  => CoreExpr
  -> CoreExpr
  -> Eff es (Either NonEq ())
exprSymEq' lhs rhs = runErrorNoCallStack @NonEq $ runFresh "fresh" do
  let lty = exprType lhs
  let rty = exprType rhs
  unless (lty `eqType` rty) $ do
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

  result <- provide_ @Solver $ solve (symNot eq)

  case result of
    Satisfiable model -> do
      let concretise' = runEvalErr . concretise model
      bndrs' <- forM bndrs concretise'
      lres' <- concretise' lres
      rres' <- concretise' rres
      throwError_ $ Counterexample bndrs' lres' rres'
    Unsatisfiable -> pure ()
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
