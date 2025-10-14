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
  ( CoreExpr
  , CoreProgram
  , Name
  , Role (..)
  , exprType
  , splitFunTys
  , showSDocUnsafe
  , targetPlatform
  , HasDynFlags (..)
  , varType
  , vcat
  , emptyInScopeSet
  , mkTyConApp
  , mkUnivCo
  , dataConWorkId
  , mkApps
  , Expr (..)
  , idUnfolding
  , Unfolding (..)
  , idInlinePragma
  , InlinePragma (..)
  , InlineSpec (..)
  , hasCoreUnfolding
  , tyConKind
  , tyConRoles
  , TyCon
  , Id
  , coercibleDataCon
  )
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  , SDoc
  , ($+$)
  , (<+>)
  , nest
  , empty
  )
import GHC.Core.Map.Expr (TrieMap(..), insertTM)
import GHC.Core.TyCon.Env (mkTyConEnv)
import GHC.Platform (PlatformWordSize (..), Platform (..))
import GHC.Core.TyCo.Rep
  ( scaledThing
  , Type (..)
  , UnivCoProvenance (..)
  )
import GHC.Tc.Utils.TcType (eqType, tcSplitSigmaTy)

import Grisette (LogicalOp (..), ModelOps (..), EvalSym (..), onUnion)

import Control.Monad (unless, (>=>))
import Control.Monad.Except (runExceptT)
import Control.Arrow (Arrow(..))

import Data.List (intersperse)
import Data.Traversable (forM, for)
import Data.Foldable (for_)
import Data.Function (on)

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
import Pantomime.Result (handle, ok)
import Pantomime.Util (withCallStack, foldM')
import Pantomime.Annotation (Theory (..))
import Pantomime.Unification (resolveCustomInstances)

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

dbg :: forall o es. Outputable o => o -> Eff es ()
dbg = unsafeEff_ . putStrLn . showSDocUnsafe . ppr

-- TODO: I'm not a big fan of this one, but it works for now. At some point,
-- I want to make this nicer.. If anything, this probably shouldn't live in this
-- module!
data Theory' where
  Theory' ::
    { tyInterp' :: [(TyCon, TyCon)]
    , idInterp' :: [(Id, Id)]
    } -> Theory'

resolveTheory
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Context Reader CoreProgram :> es
  => Theory
  -> Eff es Theory'
resolveTheory theory = do
  tyInterp' <- for (tyInterp theory) \(orig, interp) -> do
    -- let resolve = thNameToGhcName >=> lookupTyConAll
    -- TODO: Add lookup for local TyCon declarations.
    tcOrig <- Primitive.thNameToTyCon orig
    tcInterp <- Primitive.thNameToTyCon interp
    pure (tcOrig, tcInterp)

  idInterp' <- for (idInterp theory) \(orig, interp) -> do
    let resolve = thNameToGhcName >=> lookupIdAll
    idOrig <- resolve orig
    idInterp <- resolve interp
    pure (idOrig, idInterp)

  pure Theory' { .. }

-- | Extend user-supplied function interpretations with the user-supplied
-- coercion mapping.
--
-- # Example
-- Suppose the user has some bitvector type called 'Signed'.
--
-- > type Signed (n :: Nat) = ...
--
-- The user supplies the following mapping:
--
-- > Signed |-> IntN
--
-- This roughly says that the user wants to use the underlying bitvector
-- representation IntN, which is implemented using the respective SMT theory.
--
-- Now, a user has some functions that operation on 'Signed'. These of course
-- require a mapping to the their respective operation on 'IntN'. Before
-- anything, a user needs to ensure that **ALL** operations on 'Signed' are
-- through functions marked as 'OPAQUE' and that it's constructor is not
-- exported. This is to ensure correctness of within the evaluator.
--
-- To illustrate, suppose we have an addition function for 'Signed' values.
--
-- > {-# OPAQUE plusSigned #-}
-- > plusSigned :: KnownNat n => Signed n -> Signed n -> Signed n
--
-- We can write an interpretation for this using the addition as provided by
-- 'IntN'. The importance lies in using a coercion 'Signed ~ IntN'.
--
-- > plusInterp :: Coercible Signed IntN => KnownNat n => Signed n -> Signed n -> Signed n
-- > plusInterp = go
-- >   where
-- >     go :: bv ~ IntN => bv n -> bv n -> bv n
-- >     go = coerce plusIntN
--
-- Note, the where clause is only to trick Haskell into allowing the coercion
-- to appear at the top level. With this defintion in place, we supply the
-- appropriate mapping:
--
-- > plusSigned |-> plusInterp
--
-- Of course, the types for 'plusSigned' and 'plusInterp' do not match up
-- one-to-one. That is, to complete the interpretation, we need to supply
-- 'plusInterp' with the user-supplied coercion that Signed ~ IntN. Afterwards,
-- the types match up and the function is a valid interpretation.
--
-- # Usage
--
-- This function will perform this last operation of inserting the coercion
-- Signed ~ IntN, or any other user-supplied into an interpretation. It will
-- additionally ensure that the resulting mappings are correct.
--
-- Lastly, this also ensures that mappings are only made for OPAQUE functions.
-- A special case here we do allow is a NOINLINE function without an unfolding.
-- For these, we do not use any of the user-provided coercions.
coerceInterp
  :: Theory'
  -> Eff es [(Id, CoreExpr)]
coerceInterp theory = do
  -- Create a boxed coercion between the given TyCon.
  let mkPluginTcCo tcL tcR = do
        -- Get the kind of the coercible TyCon.
        let kind = tyConKind tcL

        -- Ensure the kind and roles match up.
        let eqKinds = eqType kind $ tyConKind tcR
        let eqRoles = all (uncurry (==)) $ on zip tyConRoles tcL tcR
        unless (eqKinds && eqRoles) do
          undefined

        -- Gather the remaining information to construct the coercion.
        let prov = PluginProv "pantomime user-defined"
        let tyL = mkTyConApp tcL []
        let tyR = mkTyConApp tcR []
        let co = mkUnivCo prov Representational tyL tyR

        -- Box the coercion.
        let eqVar = Var $ dataConWorkId coercibleDataCon
        pure $ mkApps eqVar [Type kind, Type tyL, Type tyR, Coercion co]

  -- Insert a coercion between two TyCon into the given dictionary.
  let insertCo tcL tcR dicts = do
        dict <- mkPluginTcCo tcL tcR
        let ty = exprType dict
        pure $ insertTM ty dict dicts

  -- Gather the dictionary map for instance resolution.
  dicts <- foldM' emptyTM (tyInterp' theory) \dicts (orig, interp) -> do
    -- Add both directions of the coercion to the dictionary map.
    insertCo orig interp >=> insertCo interp orig $ dicts

  -- Gather a binder mapping for a substitution. This will use the dictionary
  -- map to supply coercions to any Opaque values that require it.
  for (idInterp' theory) \(orig, interp) -> do
    -- Gather the expression of the interpretation.
    expr <- case idUnfolding interp of
      CoreUnfolding { uf_tmpl } -> pure uf_tmpl
      _ -> undefined

    -- Check whether the original target can be interpreted.
    expr' <- case inl_inline $ idInlinePragma orig of
      -- Opaque values can be fully interpreted. Hence, we resolve any coercions
      -- that were provided by the user.
      Opaque _ -> pure $ resolveCustomInstances dicts expr

      -- We only want to interpret no-inline if the unfolding was not available.
      NoInline _ | hasCoreUnfolding $ idUnfolding orig -> pure expr

      -- It is fragile to interpret inlineable instances, as they may already
      -- have been optimised away.
      _ -> undefined

    -- Check whether the interpretation matches.
    unless (varType orig `eqType` exprType expr') do
      undefined

    -- Return the mapping.
    pure (orig, expr')

-- Okay! I have a way to wrap functions with the plugin coercions now!
-- What do I still need?
-- 1. Pipe these mappings into the substitution environment.
-- 2. Extend the fresh variable generation to handle this mapping.
--
-- What do I need/want to do for step 1?
-- 1. I want to split the resolution of the TyCon and Ids from everything
--    else. Probably need to make a new data type or GADT the Theory type.
-- 2. Separate the remainder of this function which then returns the mapping.
--
-- What do I need/want to do for step 2?
-- 1. Create some form of map TyCon |-> TyCon given user provided mapping.
-- 2. Join all the mappings required for fresh variable generation into a
--    single value. I guess we could call it 'FreshInstEnv'? This would
--    include TyCon |-> TyCon, FamInstEnvs and Primitive.Types.
--    TODO: I still need to do this last part I think!
-- 3. We should also remove any existing reductions in the 'FamInstEnvs' no?
--    Otherwise, we might reduce using the wrong axiom. I guess the reason to
--    not use the existing axiom mechanism for TyCon |-> TyCon is strictly
--    because we want the coercion to be a plugin provenance universion
--    coercion. Something not possible if it is an axiom in the FamInstEnv.

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
  => Theory
  -> CoreExpr
  -> Eff es ()
checkValid theory expr = do
  -- TODO: Somehow this code doesn't read very nice. I think I should review it
  -- Specifically the substitution part should dictate the inner error. I guess
  -- it does now because it can also substitute types. Perhaps we can adjust
  -- extendSubstMany that is only does value substitution. This way, we can
  -- split the error type for adding from the one used in the expression itself.
  program <- get @CoreProgram

  theory' <- resolveTheory theory
  userBinds <- coerceInterp theory'

  reifiedIntN <- Primitive.reifiedIntN
  reifiedBase <- Primitive.reifiedBase

  let subst = do
        subst0 <- Pantomime.extendIdSubstMany Pantomime.mkEmptySubst reifiedIntN
        subst1 <- Pantomime.extendIdSubstMany subst0 reifiedBase
        -- TODO: I think there is an ordering problem here between user
        -- mappings and program definitions. I guess user mappings should
        -- go first? The problem is that we don't want local definitions to
        -- overwrite them. I guess for now, we can keep the ordering like this,
        -- but this essentially restricts mappings to be used only outside of
        -- their defining module. Not the worst thing though, as the functions
        -- should truly be opaque outside of the defining module and they cannot
        -- be guaranteed to not be misused within the module.
        let userBinds' = second (Pantomime.symbolise subst1) <$> userBinds
        subst2 <- Pantomime.extendIdSubstMany subst1 userBinds'
        Pantomime.symboliseBindMany subst2 program

  subst' <- case handle subst of
    -- TODO: Properly propagate error!
    Left (_cs, ()) -> undefined
    Right value -> pure $ ok value

  -- TODO: I'm pretty sure I need to still filter axioms from the family
  -- instance environment. I also feel like somehow building this here is not
  -- super nice.
  famInst <- getFamInstEnvs
  primTys <- Primitive.getTypes
  let userCo = mkTyConEnv $ tyInterp' theory'
  let freshEnv = Pantomime.FreshInstEnv
        { Pantomime.fieFam = famInst
        , Pantomime.fiePrim = primTys
        , Pantomime.fieUser = userCo
        }

  let ty = exprType expr
  let (args, _scope) = Pantomime.freshArgs freshEnv ty emptyInScopeSet

  let fun = Pantomime.symbolise subst' expr

  let result = fun >>= flip Pantomime.mkApps (snd <$> args)

  let Pantomime.Eval boolResult = result >>= Pantomime.exprToBool

  -- TODO: I was thinking of making a 'handleE' function for 'Eval', but it
  -- seems like the 'Raise' constructor prohibits this (as it also contains
  -- an error field). Still, I feel like there should be a better way to
  -- construct this...
  evalBool <- case handle boolResult of
    -- TODO: Properly propagate error!
    Left (cs, ()) -> withCallStack cs $ error "Symbolic solver error"
    Right value -> pure $ runExceptT (ok value)
    -- Right value -> pure . runExceptT . ok $ value

  -- dbg evalBool

  let eq = flip onUnion evalBool \case
        Left Pantomime.Unreachable -> true
        Left Pantomime.UB -> false
        Left Pantomime.Raise {} -> false
        Right value -> value

  solution <- provide_ @Solver $ solve (symNot eq)

  -- dbg result
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
      -- TODO: I should probably check whether the arguments are recursive
      -- before printing? Alternatively, I could just have a maximum depth.
      for_ args \(bndr, arg) -> do
        let arg' = evalSym True model arg
        dbg $ vcat
          [ "==================="
          , ppr bndr <+> "::" <+> ppr (varType bndr)
          , ppr arg'
          ]
      error "Expression was **not** valid!"
    Unsatisfiable -> do
      dbg @SDoc "Expression was valid!"
      pure ()
    -- FIXME: I don't think this is always true. Especially so w.r.t. allowing
    -- user define Opaque types. Also not sure about some of the floating point
    -- stuff for example.
    Unknown -> throwIO $ ErrorCall "checks are in decidable fragment"

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
