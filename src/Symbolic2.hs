{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Symbolic2
  ( testSymbolic
  , exprSymEq
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Map.Expr (TrieMap(..), insertTM)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Unify (tcMatchTy)
import GHC.Types.Unique.DFM (UniqDFM)
import GHC.Platform (Platform (platformWordSize), PlatformWordSize (..))
import GHC.Generics (Generic)
import GHC.Builtin.PrimOps (PrimOp (..))
import GHC.Builtin.Types.Prim
import GHC.Tc.Utils.TcType (eqType, tcSplitSigmaTy, substTy)
import GHC.MonadCore

import Control.Monad (forM, unless)
import Control.Monad.Except
import Control.Monad.State

import Data.Foldable (find, forM_)
import Data.String (IsString(..))
import Data.Functor ((<&>))
import Data.Bits (Bits(..), (.^.))

-- TODO: There has to be a better way to not import pretty printing stuff from
-- grisette...
import Grisette hiding (PPrintType (..), (<>), (<+>), nest, punctuate, comma, vcat, braces, lbrace, rbrace)
import Grisette.Internal.SymPrim.Prim.Term (ModelValue (..))

import SymUtil
import BitVec
import Debug.Trace (trace)
import Data.Composition ((.:))

-- TODO: Importantant things to do right now
-- - 'Symbolic' and 'Value' kind of feel like they should be merged. We should
-- just have one 'Value' data type.
--   - Done. What I think would be good is if Function now have some sort of
--     type attached. The current thing with Type + function that takes any
--     value doesn't seem super nice though. Ideally, I would somehow reuse the
--     Value structure for arguments. That is, we have a function that takes any
--     type of value, but then actually typed as such.
--   - Since we removed the Symbolic, should we rename some stuff from symX to
--     evalX?
--
-- - We should add support for casts and coercions. I guess this requires at
-- least a Coercion to be added as possible 'Value'. Other than that, I guess it
-- depends on whatever we should do for Cast statements.
--   - It works now, but is still very messy. I'm wondering if I really should
--     track the full coercion or just the current result type.
--
-- - We should attach type signatures to ADT in Value so we can re-construct a
-- concrete version.
--   - First part done. Now we should actually use it!
--   - I think it makes sense to do this for functions as well btw!
--
-- - Support for more primitive operations! I guess I want to encaspulate how to
-- gather arguments to minimize code duplication.

-- TODO: Some ideas:
-- - Should we also attach a type signature to functions? Then we could actually
--   print a symbolic function. It would also help with saturating it...
--
-- - How about supporting the function primitive from grisette. It seems to me
--   that it should be preferred wherever possible, as grisette probably has
--   some optimisations for it.

-- TODO: All this testing stuff is super ugly...
testSymbolic
  :: MonadCore m
  => HasDynFlags m
  => MonadFail m
  => CoreExpr
  -> m ()
testSymbolic expr = do
  dbg expr
  dflags <- getDynFlags
  -- TODO: Pass in the actual platform wordsize for the solver.
  let _wordSize = platformWordSize $ targetPlatform dflags
  -- let config = Config
  --       { wordSize = toWordSize . platformWordSize $ targetPlatform dflags
  --       }

  let s = SymbolicState
        -- { nextADT = 0
        { nextIdx = 0
        }

  symbolic <- flip evalStateT s $ runExceptT $ do
    (bndrs, result) <- saturated @_ @64 expr 
    result' <- asADT result
    pure (bndrs, result')

  (args, value) <- case symbolic of
    Right (bndrs, value) -> pure (bndrs, value)
    Left err -> fail $ "Error creating symbolic version: " ++ show err

  dbg' $ show value

  let z3' = z3
        { sbvConfig = (sbvConfig z3)
          { verbose = True
          , timing = PrintTiming
          }
        }

  result <- liftCore . liftIO $ do
    -- let f = sym "0" :: ADT -~> ADT
    let g = sym "0" :: ADT -~> SymIntN64
    -- result <- solve z3' $ (fmap ((g #) . (f #)) value) .== pure (0x10)
    let translate = \case
          -- Right val -> g # (f # val) .== 0x10
          Right val -> g # val .== 0x10
          -- TODO: I guess we want to handle Invalid differently from the other
          -- errors?
          Left _ -> false

    solveExcept z3' translate value

  result' <- case result of
    Right model -> do
      let bndrs = fst (collectBinders expr)
      bndrs' <- runExceptT $ forM (zip args bndrs) $ \(arg, bndr) -> do
        val <- concreteValue model arg
        pure $ ppr (occName bndr) <+> "=" <+> ppr val

      pure bndrs'
    Left _ -> undefined

  case result' of
    Right bndrs -> forM_ bndrs dbg
    Left err -> dbg err

exprSymEq
  :: forall m
   . MonadFail m
  => MonadCore m
  => HasDynFlags m
  => CoreExpr
  -> CoreExpr
  -> m (Either NonEq ())
exprSymEq lhs rhs = do
  -- Get the target platform word size.
  dflags <- getDynFlags
  let pwsize = platformWordSize $ targetPlatform dflags

  -- We run the comparison with the word size of the target platform.
  case pwsize of
    PW4 -> exprSymEq' @m @32 lhs rhs
    PW8 -> exprSymEq' @m @64 lhs rhs

data NonEq
  = Counterexample [ModelValue']
  | EvalError SymbolicError
  | SolveError

instance Outputable NonEq where
  ppr = \case
    Counterexample values -> vcat $ values <&> ppr
    EvalError err -> text "eval-error: " <+> ppr err
    -- TODO: More details what failed for the solver!
    SolveError -> text "solver error"

exprSymEq'
  :: forall m n
   . MonadFail m
  => MonadCore m
  => KnownPos n
  => CoreExpr
  -> CoreExpr
  -> m (Either NonEq ())
exprSymEq' lhs rhs = runExceptT $ do
  let st = SymbolicState
        { nextIdx = 0
        }

  (bndrs, lres, rres, eq) <- flip evalStateT st . modifyError EvalError $ do
    (bndrs, lresult) <- saturated @_ @n lhs
    rhs' <- eval @_ @n emptyTM rhs
    rresult <- foldM' rhs' bndrs $ \value bndr -> do
      applyValue value bndr

    dbg lhs
    case lresult of
      ADT ty val -> do
        dbg ty
        dbg' $ show val
      _ -> pure ()

    dbg rhs
    case rresult of
      ADT ty val -> do
        dbg ty
        dbg' $ show val
      _ -> pure ()

    eq <- assertEq lresult rresult
    pure (bndrs, lresult, rresult, eq)

  dbg' $ show eq

  -- TODO: We could let the user decide which solver no?
  let z3' = z3
        { sbvConfig = (sbvConfig z3)
          { verbose = True
          , timing = PrintTiming
          }
        }

  -- TODO: We should translate the model to our version!
  -- result <- liftCore . liftIO $ solve z3' eq
  let translate = \case
        Left Invalid -> false
        Right val -> symNot val
        _ -> false

  result <- liftCore . liftIO $ solveExcept z3' translate eq
  case result of
    Right model -> do
      let concreteValue' = modifyError EvalError . concreteValue model
      bndrs' <- forM bndrs concreteValue'
      lres' <- concreteValue' lres
      rres' <- concreteValue' rres
      dbg' "============="
      dbg' $ show model
      dbg' "-------------"
      dbg bndrs'
      dbg' "*************"
      dbg lres'
      dbg' "@@@@@@@@@@@@@"
      dbg rres'
      dbg' "ignore after this for now!"


      throwError $ Counterexample bndrs'
    Left Unsat -> pure ()
    Left _ -> throwError $ SolveError

-- FIXME: I don't think this works for divide by zero. I.e. if only one of the
-- two expressions fail, it should be non-equal.
assertEq
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => Value m n
  -> Value m n
  -> m (RuntimeValue SymBool)
assertEq (Int lhs) (Int rhs) = pure $ cmpRuntime lhs rhs
assertEq (Int8 lhs) (Int8 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Int16 lhs) (Int16 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Int32 lhs) (Int32 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Int64 lhs) (Int64 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word lhs) (Word rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word8 lhs) (Word8 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word16 lhs) (Word16 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word32 lhs) (Word32 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word64 lhs) (Word64 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Float lhs) (Float rhs) = pure $ cmpRuntime lhs rhs
assertEq (Double lhs) (Double rhs) = pure $ cmpRuntime lhs rhs
assertEq (ADT lty lhs) (ADT rty rhs) = do
  unless (lty `eqType` rty) $ throwError IllTyped
  (tyCon, tyArgs) <- whyFail IllTyped $ splitTyConApp_maybe lty
  let dataCons = tyConDataCons tyCon

  branches <- forM dataCons $ \dataCon -> do
    -- Ensure that we are in
    let inBranch adt = adtIsDataCon @n adt dataCon
    let eqBranch = cmpRuntime (inBranch lhs) (inBranch rhs)

    -- Gather the field names.
    let names = dataConAccessorNames dataCon
    let tys = scaledThing <$> dataConInstArgTys dataCon tyArgs
    let accessors = zip names tys

    -- Check that every field is the same.
    assertions <- forM accessors $ \(name, ty) -> do
      lfield <- accessField @m @n lhs name ty
      rfield <- accessField rhs name ty
      assertEq lfield rfield

    let assertions' = foldl' (liftA2 (.&&)) (pure true) assertions

    pure $ (eqBranch, assertions')


  let invalid = throwError Invalid

  foldM' invalid branches $ \fl (cond, rhs') -> do
    pure $ iteRuntime cond rhs' fl
assertEq (Cast' lco lhs) (Cast' rco rhs) = do
  unless (lco `eqCoercion` rco) $ throwError IllTyped
  assertEq lhs rhs
assertEq _ _ = throwError IllTyped

-- (! (ite 
--   (||
--     (distinct (apply tag x) 0x0000000000000000) 
--     (! (&&
--       (=
--         (apply 0 !ADT@0)
--         (+ 0x0000000000000001 (apply 0 x)))
--       (= (apply tag !ADT@0) 0x0000000000000000))))
--   (||
--     (distinct (apply tag x) 0x0000000000000000)
--     (! (&&
--       (=
--         (apply 0 !ADT@1)
--         (+ 0x0000000000000001 (apply 0 x)))
--       (= (apply tag !ADT@1) 0x0000000000000000))))
--   (&&
--     (&&
--       (= (apply tag x) 0x0000000000000000)
--       (&&
--         (=
--           (apply 0 !ADT@1)
--           (+ 0x0000000000000001 (apply 0 x)))
--         (= (apply tag !ADT@1) 0x0000000000000000)))
--     (= !ADT@0 !ADT@1))))
--
-- Model
--   { !ADT@0 -> 0x0000000000000000 :: WordN 64
--   , !ADT@1 -> 0x0000000000000002 :: WordN 64
--   , 0 -> \(arg@1 :: WordN 64) ->
--       (ite
--         (= arg@1 0x0000000000000002)
--         0x000004a42200830b
--         (ite
--           (= arg@1 0x0000000000000000)
--           0x000004a42200830a
--           0x0000000000000000))
--     :: (-->) (WordN 64) (IntN 64)
--   , tag -> \(arg@0 :: WordN 64) ->
--       0x0000000000000000
--     :: (-->) (WordN 64) (IntN 64)
--   , x -> 0x0000000000000000 :: WordN 64
--   }

-- -- | Compares two values whether they always give the same result.
-- --
-- -- Note that this will also check equivalence for assignments that produce
-- -- runtime errors. In these cases, equivalence is only held if both values
-- -- crash.
-- cmpSymbolic
--   :: MonadError SymbolicError m
--   => KnownPos n
--   => Value m n
--   -> Value m n
--   -> m SymBool
-- cmpSymbolic lhs' rhs' = case (lhs', rhs') of
--   (Int lhs, Int rhs) -> pure $ lhs .== rhs
--   (Int8 lhs, Int8 rhs) -> pure $ lhs .== rhs
--   (Int16 lhs, Int16 rhs) -> pure $ lhs .== rhs
--   (Int32 lhs, Int32 rhs) -> pure $ lhs .== rhs
--   (Int64 lhs, Int64 rhs) -> pure $ lhs .== rhs
--   (Word lhs, Word rhs) -> pure $ lhs .== rhs
--   (Word8 lhs, Word8 rhs) -> pure $ lhs .== rhs
--   (Word16 lhs, Word16 rhs) -> pure $ lhs .== rhs
--   (Word32 lhs, Word32 rhs) -> pure $ lhs .== rhs
--   (Word64 lhs, Word64 rhs) -> pure $ lhs .== rhs
--   (Float lhs, Float rhs) -> pure $ lhs .== rhs
--   (Double lhs, Double rhs) -> pure $ lhs .== rhs
--   (ADT lty lhs, ADT rty rhs) -> do
--     unless (lty `eqType` rty) $ throwError IllTyped
--     pure $ lhs .== rhs
--   (Cast' lco lhs, Cast' rco rhs) -> do
--     unless (lco `eqCoercion` rco) $ throwError IllTyped
--     cmpSymbolic lhs rhs
--   _ -> throwError IllTyped
--   where
    -- FIXME: Something is terminally wrong in this comparison. Both expressions
    -- generate the correct thing (and actually the same thing), but still I
    -- can find a saturating example to their non-equivalence.
    -- cmp :: SymEq a => Show a => RuntimeValue a -> RuntimeValue a -> SymBool
    -- cmp lhs rhs = onUnion id $ do
    --   lhs' <- runExceptT lhs
    --   rhs' <- runExceptT rhs
    --   case (lhs', rhs') of
    --     (Right lhs'', Right rhs'') -> trace ("LHS: " <> show lhs'') . pure $ lhs'' .== rhs''
    --     (Left lerr, Left rerr) -> pure $ con (lerr == rerr)
    --     _ -> pure false

-- TODO: I think this is not the cleanest representation. We should make this
-- a bit better.
data ModelValue' where
  Record :: DataCon -> [(String, ModelValue')] -> ModelValue'
  Primitive :: ModelValue -> ModelValue'
  Error :: RuntimeError -> ModelValue'
  -- TODO: We want to give out Unknown for recursive values. I guess we'll leave
  -- this for now...
  Unknown :: ModelValue'

-- TODO: The indentation is a bit off because we vertically nest only the
-- DataCon, while we should nest it with the assignment 'value = DataCon'.
instance Outputable ModelValue' where
  ppr = \case
    Record dataCon fields -> ppr dataCon $+$ (nest 2 . braces' . vcat $ fields')
      where
        braces' x = lbrace <+> x $+$ rbrace
        fields' = punctuate (text ", ") $ fields <&> pair
        pair (name, value) = text name <+> "=" <+> ppr value
    Primitive value -> text $ show value
    Error err -> "error value: " <+> ppr err
    Unknown -> text "???"

concreteValue
  :: forall m m' n
   . MonadError SymbolicError m
  => MonadCore m
  => KnownPos n
  => Model
  -> Value m' n
  -> m ModelValue'
concreteValue model = \case
  Int value -> prim @_ @(IntN n) value
  Int8 value -> prim @_ @IntN8 value
  Int16 value -> prim @_ @IntN16 value
  Int32 value -> prim @_ @IntN32 value
  Int64 value -> prim @_ @IntN64 value
  Word value -> prim @_ @(WordN n) value
  Word8 value -> prim @_ @WordN8 value
  Word16 value -> prim @_ @WordN16 value
  Word32 value -> prim @_ @WordN32 value
  Word64 value -> prim @_ @WordN64 value
  Float value -> prim @_ @FP32 value
  Double value -> prim @_ @FP64 value
  -- TODO: Clean this horrible piece of code up!
  ADT ty adt -> case evalSymToCon @_ @(Either RuntimeError ADT) model adt of
    Right adt' -> do
      let tag = evalSymToCon @_ @(Tag n) model $ accessTag @n adt'
      dbg' $ show tag
      case tagToDataCon tag ty of
        Just dataCon -> do
          let (_, _, funTy) = tcSplitSigmaTy $ dataConRepType dataCon
          let (argTys, resTy) = splitFunTys funTy

          -- We try to match the result type of the constructor to the case binder.
          -- Really, this should never fail.
          subst <- whyFail IllTyped $ tcMatchTy resTy ty
          let argTys' = substTy subst . scaledThing <$> argTys
          let names = dataConAccessorNames dataCon
          let accessors = zip names argTys'
          fields <- forM accessors $ \(name, ty') -> do
            field <- accessField @m @n adt name ty'
            concreteValue model field

          pure $ Record dataCon (zip names fields)
        Nothing -> pure Unknown

    Left err -> pure $ Error err

  -- TODO: Clean this horrible piece of code up!
  Cast' co value' -> go value' $ coercionRKind co
    where
      go value ty | not $ ty `eqType` coercionLKind co = do
        (tyCon, tys) <- whyFail IllTyped $ splitTyConApp_maybe ty
        dataCon <- whyFail undefined $ tyConSingleDataCon_maybe tyCon
        argTy <- case dataConInstArgTys dataCon tys of
          [argTy] -> pure $ scaledThing argTy
          _ -> throwError IllTyped
        arg' <- go value argTy
        pure $ Record dataCon [("0", arg')]
      go value _ = concreteValue model value

  -- TODO: There should be a better error to emit than this no? Maybe we
  -- should make a new one... Maybe we should make an error for concrete lookup
  -- failures. Alternatively, I guess we could actually just return the type as
  -- is no? It is actually also a concrete version in a sense.
  Fun _ -> throwError IllTyped
  Ty _ -> throwError IllTyped
  Co _ -> throwError IllTyped
  where
    prim
      :: forall a b
       . ToCon a b
      => EvalSym a
      => SupportedPrim b
      => RuntimeValue a
      -> m ModelValue'
    prim value = do
      let concrete = evalSymToCon @_ @(Either RuntimeError b) model value
      case concrete of
        Right value' -> pure $ Primitive (ModelValue value')
        Left err -> pure $ Error err

asIntN64 :: MonadError SymbolicError m => Value m n -> m (RuntimeValue SymIntN64)
asIntN64 = \case
  Int64 value -> pure value
  _ -> throwError IllTyped

asADT :: MonadError SymbolicError m => Value m n -> m (RuntimeValue ADT)
asADT = \case
  ADT _ value -> pure value
  Cast' _ value -> asADT value
  _ -> throwError IllTyped

saturated
  :: MonadSymbolic m
  => KnownPos n
  => CoreExpr
  -> m ([Value m n], Value m n)
saturated expr = do
  value <- eval emptyTM expr
  let (bndrs, _) = collectBinders expr
  symBndrs <- forM bndrs symbolicInstance
  result <- foldM' value symBndrs $ \value' bndr -> do
    applyValue value' bndr
  pure (symBndrs, result)

symbolicInstance
  :: MonadError SymbolicError m
  => KnownPos n
  => Id
  -> m (Value m n)
symbolicInstance bndr = typedValue symbolic ty
  where
    symbolic :: Solvable c a => RuntimeValue a
    symbolic = pure . sym . fromString $ name
    name = occNameString $ occName bndr
    ty = varType bndr

-- TODO: Add support for all primitive runtime errors.
-- TODO: We could add support for bottom? I guess we would want an option to
-- enable/disable bottom values for the checker then? Technically, we need to
-- deal with errors in any case, so maybe the disable should just ensure the
-- inputs are not bot?
data RuntimeError where
  DivideByZero :: RuntimeError
  -- | Any Symbolic value that cannot be reached in practise.
  --
  -- For example, we create a symbolic BigNatural via SymInteger with a
  -- constraint that the value cannot be negative. This error would be reached
  -- if the constraint solver tries to instantiate a negative number.
  Invalid :: RuntimeError
  deriving Show
  deriving Generic
  deriving Eq
  deriving Mergeable via (Default RuntimeError)
  deriving EvalSym via (Default RuntimeError)
  deriving SymEq via (Default RuntimeError)

instance Outputable RuntimeError where
  ppr = \case
    DivideByZero -> text "divide-by-zero"
    Invalid -> text "invalid"

type RuntimeValue a = ExceptT RuntimeError Union a

type ADT = SymWordN64

-- | ADT tag to distinguish between constructors.
type Tag n = SymIntN n

data SymbolicError where
  IllTyped :: SymbolicError
  UnsupportedExpr :: SymbolicError
  UnboundVariable :: SymbolicError
  deriving Show

instance Outputable SymbolicError where
  ppr = \case
    IllTyped -> text "ill-typed"
    UnsupportedExpr -> text "unsupported expression"
    UnboundVariable -> text "unbound variable"

data Value m n where
  -- Char :: RuntimeValue (SymWordN 31) -> Value m n
  -- BigNat :: RuntimeValue SymInteger -> Value m n
  Int :: RuntimeValue (SymIntN n) -> Value m n
  Int8 :: RuntimeValue SymIntN8 -> Value m n
  Int16 :: RuntimeValue SymIntN16 -> Value m n
  Int32 :: RuntimeValue SymIntN32 -> Value m n
  Int64 :: RuntimeValue SymIntN64 -> Value m n
  Word :: RuntimeValue (SymWordN n) -> Value m n
  Word8 :: RuntimeValue SymWordN8 -> Value m n
  Word16 :: RuntimeValue SymWordN16 -> Value m n
  Word32 :: RuntimeValue SymWordN32 -> Value m n
  Word64 :: RuntimeValue SymWordN64 -> Value m n
  Float :: RuntimeValue SymFP32 -> Value m n
  Double :: RuntimeValue SymFP64 -> Value m n
  ADT :: Type -> RuntimeValue ADT -> Value m n
  -- TODO: I don't really like the prime on the name of Cast here. Maybe we
  -- could co for some other name?
  Cast' :: Coercion -> Value m n -> Value m n
  Fun :: (Value m n -> m (Value m n)) -> Value m n
  Ty :: Type -> Value m n
  Co :: Coercion -> Value m n

mkCast' :: Coercion -> Value m n -> Value m n
mkCast' co = \case
  Cast' co' value -> go (mkTransCo co' co) value mkCast'
  value -> go co value Cast'
  where
    go co' value cont
      | isReflexiveCo co' = value
      | otherwise = cont co' value

type MonadSymbolic m = (MonadError SymbolicError m, MonadState SymbolicState m, MonadCore m)

newtype SymbolicState = SymbolicState
  -- { nextADT :: ADT
  { nextIdx :: Int
  }

freshADT :: MonadState SymbolicState m => m (RuntimeValue ADT)
freshADT = state $ \s -> do
  let idx = nextIdx s
  let s' = s { nextIdx = idx + 1}
  let adt = sym $ indexed "!ADT" idx
  (pure adt, s')

type Environment m n = UniqDFM Var (Value m n)

eval
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => Environment m n
  -> CoreExpr
  -> m (Value m n)
eval env = \case
  Var var | Just op <- isPrimOpId_maybe var -> symPrimOp op
  Var var | Just dataCon <- isDataConId_maybe var -> symDataCon dataCon
  Var var -> whyFail UnboundVariable $ lookupTM var env

  Lit lit -> symLiteral lit

  Lam bndr body -> pure . Fun $ \arg -> do
    -- TODO: I think it would be good to have a check here to ensure that the
    -- argument has the correct type.
    let env' = insertTM bndr arg env
    eval env' body

  App fun arg -> do
    fun' <- eval env fun
    arg' <- eval env arg
    applyValue fun' arg'

  Let (NonRec bndr arg) body -> do
    arg' <- eval env arg
    let env' = insertTM bndr arg' env
    eval env' body

  -- Perhaps we could handle these by allowing a Tick annotation to specify an
  -- invariant. Otherwise though, we don't really care about recursive
  -- definitions. I guess bounded recursion would be nice to have, but lets
  -- leave this for now.
  Let (Rec _) _ -> throwError UnsupportedExpr

  Case scrut bndr ty alts -> do
    scrut' <- eval env scrut
    let env' = insertTM bndr scrut' env

    alts' <- forM alts $ symAlt env' scrut'

    invalid <- invalidValue ty

    foldM' invalid alts' $ \fl (cond, rhs) -> do
      iteValue cond rhs fl

  Cast expr co -> do
    value <- eval env expr
    pure $ mkCast' co value

  -- Ticks do not affect evaluation, thus we can skip it.
  Tick _ expr -> eval env expr

  -- FIXME: I should substitute the type.
  Type ty -> pure $ Ty ty

  -- FIXME: I should substitute the coercion.
  Coercion co -> pure $ Co co

applyValue
  :: MonadError SymbolicError m
  => Value m n
  -> Value m n
  -> m (Value m n)
applyValue fun arg = case fun of
  Fun fun' -> fun' arg
  _ -> throwError IllTyped

-- | Return the condition to run this alternative and its symbolic rhs.
--
-- Expects the case binder to already be bound to the scrutinee in the
-- environment.
symAlt
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => Environment m n
  -> Value m n
  -> CoreAlt
  -> m (RuntimeValue SymBool, Value m n)
symAlt env scrut = \case
  Alt (DataAlt dataCon) bndrs rhs -> do
    -- Ensure the scrutinee is actually an ADT.
    scrut' <- case scrut of
      ADT _ adt -> pure adt
      _ -> throwError IllTyped

    -- Whether the "tag" field on this ADT is equivalent to the DataCon.
    let conditional = adtIsDataCon @n scrut' dataCon

    -- Gather field accessors for all binders.
    let names = dataConAccessorNames dataCon
    let accessors = zip names bndrs
    fields <- forM accessors $ \(name, bndr) -> do
      accessField scrut' name (varType bndr)

    -- Extend the environment with field accessors for each binder.
    let insertManyTM = foldl' . flip . uncurry $ insertTM
    let env' = insertManyTM env $ zip bndrs fields

    -- Evaluate the right-hand side with the extended environment.
    rhs' <- eval env' rhs

    -- Return the condition to run this branch and the symbolic right-hand side.
    pure (conditional, rhs')

  Alt (LitAlt lit) [] rhs -> do
    -- Compare the literal, to the scrutinee.
    lit' <- symLiteral lit
    conditional <- cmpValue scrut lit'

    -- Evaluate the rhs.
    rhs' <- eval env rhs

    -- Return the condition to take this branch and the branch itself.
    pure (conditional, rhs')

  Alt DEFAULT [] rhs -> do
    let conditional = case scrut of
          ADT ty adt -> do
            -- Ensure that the tag is at least in range.
            -- TODO: Should this not be a prerequisite for any ADT? I.e. that
            -- whenever we create a symbolic ADT value this should be already
            -- constrained? Not sure which is better, so I'll leave it here for
            -- now.
            let (tyCon, _) = splitTyConApp ty
            let amount = length $ tyConDataCons tyCon
            tag <- accessTag @n <$> adt
            mrgReturn $ 0 .<= tag .&& tag .< fromIntegral amount
          _ -> pure true
            
    rhs' <- eval env rhs
    pure (conditional, rhs')

  _ -> throwError UnsupportedExpr

symDataCon
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => DataCon
  -> m (Value m n)
symDataCon dataCon = do
  -- The root creates the actually symbolic DataCon using the given type
  -- instantiation.
  let root = symDataConInst dataCon

  -- The number of type arguments we actually require.
  let nUnivTys = const () <$> dataConUnivTyVars dataCon

  -- Create an n-ary function accepting types, which will be used to instantiate
  -- the data constructor.
  final <- nArity root nUnivTys $ \_ univ -> \case
    Ty ty -> pure $ ty : univ
    _ -> throwError IllTyped

  -- We start with an emtpy list of type instances.
  final []

-- | Evaluate a DataCon with the given types as its instantiation.
--
-- This will 
symDataConInst
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => DataCon
  -- ^ The DataCon for which we will create a symbolic instance.
  -> [Type]
  -- ^ The types with which we will instantiate universal quantifiers of the
  -- DataCon.
  -> m (Value m n)
symDataConInst dataCon tys = do
  -- Create a fresh identifier for the ADT.
  adt <- freshADT

  -- Gather the accessor names and instantiate the universal types to create the
  -- field accessors.
  let names = dataConAccessorNames dataCon
  let tys' = scaledThing <$> dataConInstArgTys dataCon tys
  let accessors = zip names tys'

  -- Gather the fields of the ADT.
  fields <- forM accessors $ \(name, ty) -> do
    accessField adt name ty

  -- The root is an ADT that asserts the given conditional holds.
  let root cond = do
        let ty = mkTyConApp (dataConTyCon dataCon) tys
        let value = assertRuntime cond adt
        pure $ ADT ty value

  -- Accumulate a function that takes the fields as arguments. We pass a
  -- conditional to the root that states the field accessors are equal to the
  -- actual arguments.
  final <- nArity root fields $ \field cond arg -> do
    -- Constraint the field of the ADT to be equivalent to the argument.
    extra <- cmpValue field arg
    pure $ liftA2 (.&&) extra cond

  -- As a final constraint, the ADT tag should match the given DataCon.
  final $ adtIsDataCon @n adt dataCon

-- | Create a function with the arity of whatever we are folding over.
--
-- Use the accumulation function to pass values to pass down values to the root
-- value of the function. We do it in this way as we cannot just pass values
-- into a lambda.
nArity
  :: forall m t n a b
   . Monad m
  => Foldable t
  => (b -> m (Value m n))
  -- ^ Root value and what we accumulate.
  -> t a
  -- ^ What we fold over. Decides the arity of the function.
  -> (a -> b -> Value m n -> m b)
  -- ^ Accumulation function
  -> m (b -> m (Value m n))
nArity acc xs f = foldM' acc xs $ \acc' x -> do
  -- FIXME: I want to ensure the argument is always the actual ADT we expect.
  -- Also, I have to pass in the types for this one with the new setup.
  pure $ \y -> pure . Fun $ \arg -> do
    res <- f x y arg
    acc' res

-- | Get the DataCon from the Tag and Type.
tagToDataCon
  :: forall n
   . KnownPos n
  => Tag n
  -> Type
  -> Maybe DataCon
tagToDataCon tag ty = do
  (tyCon, _) <- splitTyConApp_maybe ty
  dataCons <- tyConDataCons_maybe tyCon
  let cmp dataCon = dataConToTag @n dataCon == tag
  find cmp dataCons

-- | Get the symbolic representation of the DataCon.
dataConToTag :: KnownPos n => DataCon -> Tag n
dataConToTag = fromIntegral . dataConTagZ

-- | Whether the given ADT matches the DataCon.
--
-- Note, this does not typecheck whether the ADT actually matches the DataCon.
-- TODO: I do want this to perform a typecheck! I would need to include the
-- type on an ADT first.
adtIsDataCon
  :: forall n
   . KnownPos n
  => RuntimeValue ADT
  -> DataCon
  -> RuntimeValue SymBool
adtIsDataCon adt dataCon = do
  field <- accessTag <$> adt
  let tag = dataConToTag @n dataCon
  mrgReturn $ field .== tag

-- | Accessor for the tag of an ADT.
accessTag
  :: forall n
   . KnownPos n
  => ADT
  -> Tag n
accessTag adt = do
  let tag = "tag" :: ADT -~> Tag n
  tag # adt

-- | Accessor for a field of an ADT.
--
-- The field is a pair of name and its result type.
-- TODO: We should create a Field data structure as they're kind of
-- interconnected. It would make the calls of this function a bit cleaner.
accessField
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => RuntimeValue ADT
  -> String
  -> Type
  -> m (Value m n)
accessField adt name ty
  -- TODO: Why can we not pass 'construct' to 'typedValue'? I don't understand
  -- why it has overlapping instances... For now, we just duplicate some code...
  | ty `eqType` intPrimTy = pure $ Int construct
  | ty `eqType` int8PrimTy = pure $ Int8 construct
  | ty `eqType` int16PrimTy = pure $ Int16 construct
  | ty `eqType` int32PrimTy = pure $ Int32 construct
  | ty `eqType` int64PrimTy = pure $ Int64 construct
  | ty `eqType` wordPrimTy = pure $ Word construct
  | ty `eqType` word8PrimTy = pure $ Word8 construct
  | ty `eqType` word16PrimTy = pure $ Word16 construct
  | ty `eqType` word32PrimTy = pure $ Word32 construct
  | ty `eqType` word64PrimTy = pure $ Word64 construct
  | ty `eqType` floatPrimTy = pure $ Float construct
  | ty `eqType` doublePrimTy = pure $ Double construct
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (ty', co) <- instNewTyCon_maybe tyCon tys = do
    value <- accessField adt name ty'
    let co' = mkSymCo co
    pure $ mkCast' co' value
  | Just _ <- tcSplitTyConApp_maybe ty = pure $ ADT ty construct
  | otherwise = throwError UnsupportedExpr
  where
    construct
      :: forall c t
       . Solvable (WordN64 --> c) (ADT -~> t)
      => RuntimeValue t
    construct = do
      let symbol = simple . identifier . fromString $ name
      let accessor = sym symbol :: ADT -~> t
      adt' <- adt
      pure $ accessor # adt'

dataConAccessorNames :: DataCon -> [String]
dataConAccessorNames dataCon = do
  -- TODO: Note sure if we want to emit fields with pprUnsafe. I think we just
  -- want the plain old name as typed in Haskell.
  let names = showPprUnsafe . flSelector <$> dataConFieldLabels dataCon
  let arity = dataConRepArity dataCon
  if
    | arity > length names -> show <$> [0..arity-1]
    | otherwise -> names

-- | Compare two values, if they are of the same type.
cmpValue
  :: MonadError SymbolicError m
  => KnownPos n
  => Value m n
  -> Value m n
  -> m (RuntimeValue SymBool)
cmpValue (Int lhs) (Int rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Int8 lhs) (Int8 rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Int16 lhs) (Int16 rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Int32 lhs) (Int32 rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Int64 lhs) (Int64 rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Word lhs) (Word rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Word8 lhs) (Word8 rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Word16 lhs) (Word16 rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Word32 lhs) (Word32 rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Word64 lhs) (Word64 rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Float lhs) (Float rhs) = pure $ cmpRuntime lhs rhs
cmpValue (Double lhs) (Double rhs) = pure $ cmpRuntime lhs rhs
cmpValue (ADT lty lhs) (ADT rty rhs) = do
  unless (lty `eqType` rty) $ throwError IllTyped
  pure $ cmpRuntime lhs rhs
cmpValue (Cast' lco lhs) (Cast' rco rhs) = do
  unless (lco `eqCoercion` rco) $ throwError IllTyped
  cmpValue lhs rhs
cmpValue _ _ = throwError IllTyped

-- | Compare two runtime values.
--
-- Note that this is different from normal symbolic equivalence in that we do
-- not want to compare error values. An error in a branch should be propagated
-- the root. This function propagates errors in either value and compares them
-- if both are non-error values.
cmpRuntime
  :: Mergeable a
  => SymEq a
  => RuntimeValue a
  -> RuntimeValue a
  -> RuntimeValue SymBool
cmpRuntime lhs rhs =
  lhs .>>= \lhs' ->
  rhs .>>= \rhs' ->
  mrgReturn $ lhs' .== rhs'

-- | Branch over a runtime symbolic boolean.
--
-- If the conditional of an if statement can fail, we first wish to check this
-- before proceeding to choose either branch. This function captures that idea.
iteRuntime
  :: SimpleMergeable a
  => RuntimeValue SymBool
  -> RuntimeValue a
  -> RuntimeValue a
  -> RuntimeValue a
iteRuntime cond tr fl =
  cond .>>= \cond' ->
  mrgIte cond' tr fl

-- | Assert that the given condition holds.
-- FIXME: This should respect lazy semantics. The current implementation
-- forces the conditional, which is not what we want from an assert. Assertions
-- should not force evaluation, but just restrict computation given no failure
-- occurred. Maybe the problem is in the comparison function cmpRuntime btw.
-- I'll have to think about it once I add support for bottom values.
assertRuntime
  :: SimpleMergeable a
  => RuntimeValue SymBool
  -> RuntimeValue a
  -> RuntimeValue a
assertRuntime cond tr = iteRuntime cond tr $ throwError Invalid

iteValue
  :: forall m n
   . KnownPos n
  => MonadError SymbolicError m
  => RuntimeValue SymBool
  -> Value m n
  -> Value m n
  -> m (Value m n)
iteValue cond (Int lhs) (Int rhs) = pure . Int $ iteRuntime cond lhs rhs
iteValue cond (Int8 lhs) (Int8 rhs) = pure . Int8 $ iteRuntime cond lhs rhs
iteValue cond (Int16 lhs) (Int16 rhs) = pure . Int16 $ iteRuntime cond lhs rhs
iteValue cond (Int32 lhs) (Int32 rhs) = pure . Int32 $ iteRuntime cond lhs rhs
iteValue cond (Int64 lhs) (Int64 rhs) = pure . Int64 $ iteRuntime cond lhs rhs
iteValue cond (Word lhs) (Word rhs) = pure . Word $ iteRuntime cond lhs rhs
iteValue cond (Word8 lhs) (Word8 rhs) = pure . Word8 $ iteRuntime cond lhs rhs
iteValue cond (Word16 lhs) (Word16 rhs) = pure . Word16 $ iteRuntime cond lhs rhs
iteValue cond (Word32 lhs) (Word32 rhs) = pure . Word32 $ iteRuntime cond lhs rhs
iteValue cond (Word64 lhs) (Word64 rhs) = pure . Word64 $ iteRuntime cond lhs rhs
iteValue cond (ADT lty lhs) (ADT rty rhs) = do
  unless (lty `eqType` rty) $ throwError IllTyped
  pure . ADT lty $ iteRuntime cond lhs rhs
iteValue cond (Cast' lco lhs) (Cast' rco rhs) = do
  unless (lco `eqCoercion` rco) $ throwError IllTyped
  result <- iteValue cond lhs rhs
  pure $ Cast' lco result
iteValue cond (Fun lhs) (Fun rhs) = do
  pure . Fun $ \arg -> do
    lhs' <- lhs arg
    rhs' <- rhs arg
    iteValue cond lhs' rhs'
iteValue _ _ _ = throwError IllTyped

-- | Get the Haskell Type or Kind corresponding to the current value.
valueType
  :: forall m n
   . Value m n
  -> Kind
valueType = \case
  Int _ -> intPrimTy
  Int8 _ -> int8PrimTy
  Int16 _ -> int16PrimTy
  Int32 _ -> int32PrimTy
  Int64 _ -> int64PrimTy
  Word _ -> wordPrimTy
  Word8 _ -> word8PrimTy
  Word16 _ -> word16PrimTy
  Word32 _ -> word32PrimTy
  Word64 _ -> word64PrimTy
  Float _ -> floatPrimTy
  Double _ -> doublePrimTy
  ADT ty _ -> ty
  Cast' co _ -> coercionRKind co
  -- FIXME: The function just tracks the argument type. I guess we could have it
  -- track the full type. Not sure what the alternative would be...
  Fun _ -> undefined
  Ty ty -> typeKind ty
  Co co -> coercionType co

-- TODO: I guess this should just return a maybe, as there is only one reason
-- why this would possibly fail.
typedValue
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => (forall c a. Solvable c a => RuntimeValue a)
  -> Type
  -> m (Value m n)
typedValue value ty
  | ty `eqType` intPrimTy = pure $ Int value
  | ty `eqType` int8PrimTy = pure $ Int8 value
  | ty `eqType` int16PrimTy = pure $ Int16 value
  | ty `eqType` int32PrimTy = pure $ Int32 value
  | ty `eqType` int64PrimTy = pure $ Int64 value
  | ty `eqType` wordPrimTy = pure $ Word value
  | ty `eqType` word8PrimTy = pure $ Word8 value
  | ty `eqType` word16PrimTy = pure $ Word16 value
  | ty `eqType` word32PrimTy = pure $ Word32 value
  | ty `eqType` word64PrimTy = pure $ Word64 value
  | ty `eqType` floatPrimTy = pure $ Float value
  | ty `eqType` doublePrimTy = pure $ Double value
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (ty', co) <- instNewTyCon_maybe tyCon tys = do
    value' <- typedValue value ty'
    let co' = mkSymCo co
    pure $ mkCast' co' value'
  | Just _ <- tcSplitTyConApp_maybe ty = pure $ ADT ty value
  | Just (_, _, _, res) <- splitFunTy_maybe ty = do
    let fun _ = typedValue value res
    pure $ Fun fun
  | otherwise = throwError UnsupportedExpr

-- | A value that should not be reachable.
--
-- It will be typed according to the given core type.
invalidValue 
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => Type
  -> m (Value m n)
invalidValue = typedValue $ throwError Invalid

-- -- TODO: Add support for all primitive operations.
-- symPrimOp
--   :: forall m n
--    . MonadError SymbolicError m
--   => PrimOp
--   -> m (Value m n)
-- symPrimOp = \case
--   Int64AddOp ->
--     pure . Fun $ \case
--       Int64 lhs -> pure . Fun $ \case
--         Int64 rhs -> pure . Int64 $ do
--           lhs' <- lhs
--           rhs' <- rhs
--           mrgReturn $ lhs' + rhs'
--         _ -> throwError IllTyped
--       _ -> throwError IllTyped
--   Int64QuotOp ->
--     pure . Fun $ \case
--       Int64 lhs -> pure . Fun $ \case
--         Int64 rhs -> pure . Int64 $ do
--           lhs' <- lhs
--           rhs' <- rhs
--           mrgModifyError (const DivideByZero) $ do
--             safeQuot @ArithException lhs' rhs'
--         _ -> throwError IllTyped
--       _ -> throwError IllTyped
--   _ -> throwError UnsupportedExpr

-- | Get the dynamically typed, symbolic function for a primitive operation.
symPrimOp
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => PrimOp
  -> m (Value m n)
symPrimOp = \case
  CharGtOp -> throwError UnsupportedExpr
  CharGeOp -> throwError UnsupportedExpr
  CharEqOp -> throwError UnsupportedExpr
  CharNeOp -> throwError UnsupportedExpr
  CharLtOp -> throwError UnsupportedExpr
  CharLeOp -> throwError UnsupportedExpr
  OrdOp -> throwError UnsupportedExpr
  Int8ToIntOp -> unary $ toIntArch @8
  IntToInt8Op -> unary $ toIntSized @8
  Int8NegOp -> unary $ negate @SymIntN8
  Int8AddOp -> binary $ (+) @SymIntN8
  Int8SubOp -> binary $ (-) @SymIntN8
  Int8MulOp -> binary $ (*) @SymIntN8
  Int8QuotOp -> throwError UnsupportedExpr
  Int8RemOp -> throwError UnsupportedExpr
  Int8QuotRemOp -> throwError UnsupportedExpr
  Int8SllOp -> binary $ symShiftL' @SymIntN @8
  Int8SraOp -> binary $ symShiftRA' @SymIntN @8
  Int8SrlOp -> binary $ symShiftRL' @SymIntN @8
  Int8ToWord8Op -> unary $ toUnsigned @SymWordN8 @SymIntN8
  Int8EqOp -> binary $ symEq @SymIntN8
  Int8GeOp -> binary $ symGe @SymIntN8
  Int8GtOp -> binary $ symGt @SymIntN8
  Int8LeOp -> binary $ symLe @SymIntN8
  Int8LtOp -> binary $ symLt @SymIntN8
  Int8NeOp -> binary $ symNe @SymIntN8
  Word8ToWordOp -> unary $ toWordArch @8
  WordToWord8Op -> unary $ toWordSized @8
  Word8AddOp -> binary $ (+) @SymWordN8
  Word8SubOp -> binary $ (-) @SymWordN8
  Word8MulOp -> binary $ (*) @SymWordN8
  Word8QuotOp -> throwError UnsupportedExpr
  Word8RemOp -> throwError UnsupportedExpr
  Word8QuotRemOp -> throwError UnsupportedExpr
  Word8AndOp -> binary $ (.&.) @SymWordN8
  Word8OrOp -> binary $ (.|.) @SymWordN8
  Word8XorOp -> binary $ (.^.) @SymWordN8
  Word8NotOp -> unary $ complement @SymWordN8
  Word8SllOp -> binary $ symShiftL' @SymWordN @8
  Word8SrlOp -> binary $ symShiftRL' @SymWordN @8
  Word8ToInt8Op -> unary $ toSigned @SymWordN8 @SymIntN8
  Word8EqOp -> binary $ symEq @SymWordN8
  Word8GeOp -> binary $ symGe @SymWordN8
  Word8GtOp -> binary $ symGt @SymWordN8
  Word8LeOp -> binary $ symLe @SymWordN8
  Word8LtOp -> binary $ symLt @SymWordN8
  Word8NeOp -> binary $ symNe @SymWordN8
  Int16ToIntOp -> unary $ toIntArch @16
  IntToInt16Op -> unary $ toIntSized @16
  Int16NegOp -> unary $ negate @SymIntN16
  Int16AddOp -> binary $ (+) @SymIntN16
  Int16SubOp -> binary $ (-) @SymIntN16
  Int16MulOp -> binary $ (*) @SymIntN16
  Int16QuotOp -> throwError UnsupportedExpr
  Int16RemOp -> throwError UnsupportedExpr
  Int16QuotRemOp -> throwError UnsupportedExpr
  Int16SllOp -> binary $ symShiftL' @SymIntN @16
  Int16SraOp -> binary $ symShiftRA' @SymIntN @16
  Int16SrlOp -> binary $ symShiftRL' @SymIntN @16
  Int16ToWord16Op -> unary $ toUnsigned @SymWordN16 @SymIntN16
  Int16EqOp -> binary $ symEq @SymIntN16
  Int16GeOp -> binary $ symGe @SymIntN16
  Int16GtOp -> binary $ symGt @SymIntN16
  Int16LeOp -> binary $ symLe @SymIntN16
  Int16LtOp -> binary $ symLt @SymIntN16
  Int16NeOp -> binary $ symNe @SymIntN16
  Word16ToWordOp -> unary $ toWordArch @16
  WordToWord16Op -> unary $ toWordSized @16
  Word16AddOp -> binary $ (+) @SymWordN16
  Word16SubOp -> binary $ (-) @SymWordN16
  Word16MulOp -> binary $ (*) @SymWordN16
  Word16QuotOp -> throwError UnsupportedExpr
  Word16RemOp -> throwError UnsupportedExpr
  Word16QuotRemOp -> throwError UnsupportedExpr
  Word16AndOp -> binary $ (.&.) @SymWordN16
  Word16OrOp -> binary $ (.|.) @SymWordN16
  Word16XorOp -> binary $ (.^.) @SymWordN16
  Word16NotOp -> unary $ complement @SymWordN16
  Word16SllOp -> binary $ symShiftL' @SymWordN @16
  Word16SrlOp -> binary $ symShiftRL' @SymWordN @16
  Word16ToInt16Op -> unary $ toSigned @SymWordN16 @SymIntN16
  Word16EqOp -> binary $ symEq @SymWordN16
  Word16GeOp -> binary $ symGe @SymWordN16
  Word16GtOp -> binary $ symGt @SymWordN16
  Word16LeOp -> binary $ symLe @SymWordN16
  Word16LtOp -> binary $ symLt @SymWordN16
  Word16NeOp -> binary $ symNe @SymWordN16
  Int32ToIntOp -> unary $ toIntArch @32
  IntToInt32Op -> unary $ toIntSized @32
  Int32NegOp -> unary $ negate @SymIntN32
  Int32AddOp -> binary $ (+) @SymIntN32
  Int32SubOp -> binary $ (-) @SymIntN32
  Int32MulOp -> binary $ (*) @SymIntN32
  Int32QuotOp -> throwError UnsupportedExpr
  Int32RemOp -> throwError UnsupportedExpr
  Int32QuotRemOp -> throwError UnsupportedExpr
  Int32SllOp -> binary $ symShiftL' @SymIntN @32
  Int32SraOp -> binary $ symShiftRA' @SymIntN @32
  Int32SrlOp -> binary $ symShiftRL' @SymIntN @32
  Int32ToWord32Op -> unary $ toUnsigned @SymWordN32 @SymIntN32
  Int32EqOp -> binary $ symEq @SymIntN32
  Int32GeOp -> binary $ symGe @SymIntN32
  Int32GtOp -> binary $ symGt @SymIntN32
  Int32LeOp -> binary $ symLe @SymIntN32
  Int32LtOp -> binary $ symLt @SymIntN32
  Int32NeOp -> binary $ symNe @SymIntN32
  Word32ToWordOp -> unary $ toWordArch @32
  WordToWord32Op -> unary $ toWordSized @32
  Word32AddOp -> binary $ (+) @SymWordN32
  Word32SubOp -> binary $ (-) @SymWordN32
  Word32MulOp -> binary $ (*) @SymWordN32
  Word32QuotOp -> throwError UnsupportedExpr
  Word32RemOp -> throwError UnsupportedExpr
  Word32QuotRemOp -> throwError UnsupportedExpr
  Word32AndOp -> binary $ (.&.) @SymWordN32
  Word32OrOp -> binary $ (.|.) @SymWordN32
  Word32XorOp -> binary $ (.^.) @SymWordN32
  Word32NotOp -> unary $ complement @SymWordN32
  Word32SllOp -> binary $ symShiftL' @SymWordN @32
  Word32SrlOp -> binary $ symShiftRL' @SymWordN @32
  Word32ToInt32Op -> unary $ toSigned @SymWordN32 @SymIntN32
  Word32EqOp -> binary $ symEq @SymWordN32
  Word32GeOp -> binary $ symGe @SymWordN32
  Word32GtOp -> binary $ symGt @SymWordN32
  Word32LeOp -> binary $ symLe @SymWordN32
  Word32LtOp -> binary $ symLt @SymWordN32
  Word32NeOp -> binary $ symNe @SymWordN32
  Int64ToIntOp -> unary $ toIntArch @64
  IntToInt64Op -> unary $ toIntSized @64
  Int64NegOp -> unary $ negate @SymIntN64
  Int64AddOp -> binary $ (+) @SymIntN64
  Int64SubOp -> binary $ (-) @SymIntN64
  Int64MulOp -> binary $ (*) @SymIntN64
  Int64QuotOp -> throwError UnsupportedExpr
  Int64RemOp -> throwError UnsupportedExpr
  Int64SllOp -> binary $ symShiftL' @SymIntN @64
  Int64SraOp -> binary $ symShiftRA' @SymIntN @64
  Int64SrlOp -> binary $ symShiftRL' @SymIntN @64
  Int64ToWord64Op -> unary $ toUnsigned @SymWordN64 @SymIntN64
  Int64EqOp -> binary $ symEq @SymIntN64
  Int64GeOp -> binary $ symGe @SymIntN64
  Int64GtOp -> binary $ symGt @SymIntN64
  Int64LeOp -> binary $ symLe @SymIntN64
  Int64LtOp -> binary $ symLt @SymIntN64
  Int64NeOp -> binary $ symNe @SymIntN64
  Word64ToWordOp -> unary $ toWordArch @64
  WordToWord64Op -> unary $ toWordSized @64
  Word64AddOp -> binary $ (+) @SymWordN64
  Word64SubOp -> binary $ (-) @SymWordN64
  Word64MulOp -> binary $ (*) @SymWordN64
  Word64QuotOp -> throwError UnsupportedExpr
  Word64RemOp -> throwError UnsupportedExpr
  Word64AndOp -> binary $ (.&.) @SymWordN64
  Word64OrOp -> binary $ (.|.) @SymWordN64
  Word64XorOp -> binary $ (.^.) @SymWordN64
  Word64NotOp -> unary $ complement @SymWordN64
  Word64SllOp -> binary $ symShiftL' @SymWordN @64
  Word64SrlOp -> binary $ symShiftRL' @SymWordN @64
  Word64ToInt64Op -> unary $ toSigned @SymWordN64 @SymIntN64
  Word64EqOp -> binary $ symEq @SymWordN64
  Word64GeOp -> binary $ symGe @SymWordN64
  Word64GtOp -> binary $ symGt @SymWordN64
  Word64LeOp -> binary $ symLe @SymWordN64
  Word64LtOp -> binary $ symLt @SymWordN64
  Word64NeOp -> binary $ symNe @SymWordN64
  IntAddOp -> binary $ (+) @(SymIntArch n)
  IntSubOp -> binary $ (-) @(SymIntArch n)
  IntMulOp -> binary $ (*) @(SymIntArch n)
  IntMul2Op -> throwError UnsupportedExpr
  IntMulMayOfloOp -> throwError UnsupportedExpr
  IntQuotOp -> throwError UnsupportedExpr
  IntRemOp -> throwError UnsupportedExpr
  IntQuotRemOp -> throwError UnsupportedExpr
  IntAndOp -> binary $ (.&.) @(SymIntArch n)
  IntOrOp -> binary $ (.|.) @(SymIntArch n)
  IntXorOp -> binary $ (.^.) @(SymIntArch n)
  IntNotOp -> unary $ complement @(SymIntArch n)
  IntNegOp -> unary $ negate @(SymIntArch n)
  IntAddCOp -> throwError UnsupportedExpr
  IntSubCOp -> throwError UnsupportedExpr
  IntGtOp -> binary $ symGt @(SymWordArch n)
  IntGeOp -> binary $ symGe @(SymWordArch n)
  IntEqOp -> binary $ symEq @(SymWordArch n)
  IntNeOp -> binary $ symNe @(SymWordArch n)
  IntLtOp -> binary $ symLt @(SymWordArch n)
  IntLeOp -> binary $ symLe @(SymWordArch n)
  ChrOp -> throwError UnsupportedExpr
  IntToWordOp -> unary $ toUnsigned @(SymWordArch n) @(SymIntArch n)
  IntToFloatOp -> throwError UnsupportedExpr
  IntToDoubleOp -> throwError UnsupportedExpr
  WordToFloatOp -> throwError UnsupportedExpr
  WordToDoubleOp -> throwError UnsupportedExpr
  IntSllOp -> binary $ symShiftL' @SymIntArch @n
  IntSraOp -> binary $ symShiftRA' @SymIntArch @n
  IntSrlOp -> binary $ symShiftRL' @SymIntArch @n
  WordAddOp -> binary $ (+) @(SymWordArch n)
  WordAddCOp -> throwError UnsupportedExpr
  WordSubCOp -> throwError UnsupportedExpr
  WordAdd2Op -> throwError UnsupportedExpr
  WordSubOp -> binary $ (-) @(SymWordArch n)
  WordMulOp -> binary $ (*) @(SymWordArch n)
  WordMul2Op -> throwError UnsupportedExpr
  WordQuotOp -> throwError UnsupportedExpr
  WordRemOp -> throwError UnsupportedExpr
  WordQuotRemOp -> throwError UnsupportedExpr
  WordQuotRem2Op -> throwError UnsupportedExpr
  WordAndOp -> binary $ (.&.) @(SymWordArch n)
  WordOrOp -> binary $ (.|.) @(SymWordArch n)
  WordXorOp -> binary $ (.^.) @(SymWordArch n)
  WordNotOp -> unary $ complement @(SymWordArch n)
  WordSllOp -> binary $ symShiftL' @SymWordArch @n
  WordSrlOp -> binary $ symShiftRL' @SymWordArch @n
  WordToIntOp -> unary $ toSigned @(SymWordArch n) @(SymIntArch n)
  WordGtOp -> binary $ symGt @(SymWordArch n)
  WordGeOp -> binary $ symGe @(SymWordArch n)
  WordEqOp -> binary $ symEq @(SymWordArch n)
  WordNeOp -> binary $ symNe @(SymWordArch n)
  WordLtOp -> binary $ symLt @(SymWordArch n)
  WordLeOp -> binary $ symLe @(SymWordArch n)
  TagToEnumOp -> pure . Fun $ \case
    Ty ty -> pure . Fun $ \case
      Int tag -> do
        adt <- freshADT
        let cond = do
              adt' <- adt
              tag' <- tag
              pure $ accessTag adt' .== tag'
        pure . ADT ty $ assertRuntime cond adt
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError UnsupportedExpr
  where
    symShiftRL'
      :: forall bv i
       . SymFromIntegral (SymWordN i) (bv i)
      => SymFromIntegral (bv i) (SymWordN i)
      => KnownPos i
      => bv i
      -> SymIntArch n
      -> bv i
    symShiftRL' lhs rhs = symShiftRL lhs $ unSymIntArch rhs

    symShiftRA'
      :: forall bv i
       . SymFromIntegral (SymIntN i) (bv i)
      => SymFromIntegral (bv i) (SymIntN i)
      => KnownPos i
      => bv i
      -> SymIntArch n
      -> bv i
    symShiftRA' lhs rhs = symShiftRA lhs $ unSymIntArch rhs

    symShiftL'
      :: forall bv i
       . SymFromIntegral (SymIntN i) (bv i)
      => SymShift (bv i)
      => KnownPos i
      => bv i
      -> SymIntArch n
      -> bv i
    symShiftL' lhs rhs = symShiftL lhs $ unSymIntArch rhs

    toIntArch :: KnownPos i => SymIntN i -> SymIntArch n
    toIntArch = SymIntArch . sizedBVResize

    toIntSized :: KnownPos i => SymIntArch n -> SymIntN i
    toIntSized = sizedBVResize . unSymIntArch

    toWordArch :: KnownPos i => SymWordN i -> SymWordArch n
    toWordArch = SymWordArch . sizedBVResize

    toWordSized :: KnownPos i => SymWordArch n -> SymWordN i
    toWordSized = sizedBVResize . unSymWordArch

    symGe :: SymOrd a => a -> a -> SymIntArch n
    symGe lhs rhs = SymIntArch $ symIte (lhs .>= rhs) 1 0

    symGt :: SymOrd a => a -> a -> SymIntArch n
    symGt lhs rhs = SymIntArch $ symIte (lhs .> rhs) 1 0

    symEq :: SymEq a => a -> a -> SymIntArch n
    symEq lhs rhs = SymIntArch $ symIte (lhs .== rhs) 1 0

    symNe :: SymEq a => a -> a -> SymIntArch n
    symNe lhs rhs = SymIntArch $ symIte (lhs ./= rhs) 1 0

    symLt :: SymOrd a => a -> a -> SymIntArch n
    symLt lhs rhs = SymIntArch $ symIte (lhs .< rhs) 1 0

    symLe :: SymOrd a => a -> a -> SymIntArch n
    symLe lhs rhs = SymIntArch $ symIte (lhs .<= rhs) 1 0

binary
  :: Wrap m n (RuntimeValue a -> RuntimeValue b -> RuntimeValue c)
  => (a -> b -> c)
  -> m (Value m n)
binary = pure . wrap . liftA2 @(ExceptT RuntimeError Union)

unary
  :: Wrap m n (RuntimeValue a -> RuntimeValue b)
  => (a -> b)
  -> m (Value m n)
unary = pure . wrap . fmap @(ExceptT RuntimeError Union)

-- TODO: This stuff is probably better suited in a separate file.
class MonadSymbolic m => Wrap m n a where
  wrap :: a -> Value m n

newtype SymIntArch n where
  SymIntArch :: SymIntN n -> SymIntArch n

unSymIntArch :: SymIntArch n -> SymIntN n
unSymIntArch (SymIntArch val) = val

deriving via SymIntN n instance KnownPos n => Num (SymIntArch n)
deriving via SymIntN n instance KnownPos n => Eq (SymIntArch n)
deriving via SymIntN n instance KnownPos n => Bits (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymOrd (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymEq (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymShift (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymFromIntegral (SymIntN n) (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymFromIntegral (SymWordN n) (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymFromIntegral (SymIntArch n) (SymIntN n)
deriving via SymIntN n instance KnownPos n => SymFromIntegral (SymWordArch n) (SymIntN n)

newtype SymWordArch n where
  SymWordArch :: SymWordN n -> SymWordArch n

unSymWordArch :: SymWordArch n -> SymWordN n
unSymWordArch (SymWordArch val) = val

deriving via SymWordN n instance KnownPos n => Num (SymWordArch n)
deriving via SymWordN n instance KnownPos n => Eq (SymWordArch n)
deriving via SymWordN n instance KnownPos n => Bits (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymOrd (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymEq (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymShift (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymFromIntegral (SymIntN n) (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymFromIntegral (SymWordN n) (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymFromIntegral (SymWordArch n) (SymWordN n)
deriving via SymWordN n instance KnownPos n => SymFromIntegral (SymIntArch n) (SymWordN n)

instance KnownPos n => SignConversion (SymWordArch n) (SymIntArch n) where
  toUnsigned = SymWordArch . toUnsigned . unSymIntArch
  toSigned = SymIntArch . toSigned . unSymWordArch

instance (MonadSymbolic m, KnownPos n) => Wrap m n (RuntimeValue (SymIntArch n)) where
  wrap = Int . fmap unSymIntArch

instance MonadSymbolic m => Wrap m n (RuntimeValue SymIntN8) where
  wrap = Int8

instance MonadSymbolic m => Wrap m n (RuntimeValue SymIntN16) where
  wrap = Int16

instance MonadSymbolic m => Wrap m n (RuntimeValue SymIntN32) where
  wrap = Int32

instance MonadSymbolic m => Wrap m n (RuntimeValue SymIntN64) where
  wrap = Int64

instance (MonadSymbolic m, KnownPos n) => Wrap m n (RuntimeValue (SymWordArch n)) where
  wrap = Word . fmap unSymWordArch

instance MonadSymbolic m => Wrap m n (RuntimeValue SymWordN8) where
  wrap = Word8

instance MonadSymbolic m => Wrap m n (RuntimeValue SymWordN16) where
  wrap = Word16

instance MonadSymbolic m => Wrap m n (RuntimeValue SymWordN32) where
  wrap = Word32

instance MonadSymbolic m => Wrap m n (RuntimeValue SymWordN64) where
  wrap = Word64

instance (MonadSymbolic m, KnownPos n, Wrap m n b) => Wrap m n (RuntimeValue (SymIntArch n) -> b) where
  wrap f = Fun $ \case
    Int arg -> pure $ wrap @m @n (f $ arg <&> SymIntArch)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymIntN8 -> b) where
  wrap f = Fun $ \case
    Int8 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymIntN16 -> b) where
  wrap f = Fun $ \case
    Int16 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymIntN32 -> b) where
  wrap f = Fun $ \case
    Int32 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymIntN64 -> b) where
  wrap f = Fun $ \case
    Int64 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, KnownPos n, Wrap m n b) => Wrap m n (RuntimeValue (SymWordArch n) -> b) where
  wrap f = Fun $ \case
    Word arg -> pure $ wrap @m @n (f $ arg <&> SymWordArch)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymWordN8 -> b) where
  wrap f = Fun $ \case
    Word8 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymWordN16 -> b) where
  wrap f = Fun $ \case
    Word16 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymWordN32 -> b) where
  wrap f = Fun $ \case
    Word32 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymWordN64 -> b) where
  wrap f = Fun $ \case
    Word64 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

-- | Get the dynamically typed, symbolic value for a literal.
symLiteral
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => Literal
  -> m (Value m n)
symLiteral = \case
  LitNumber ty num -> case ty of
    LitNumInt -> pure $ Int num'
    LitNumInt8 -> pure $ Int8 num'
    LitNumInt16 -> pure $ Int16 num'
    LitNumInt32 -> pure $ Int32 num'
    LitNumInt64 -> pure $ Int64 num'
    LitNumWord -> pure $ Word num'
    LitNumWord8 -> pure $ Word8 num'
    LitNumWord16 -> pure $ Word16 num'
    LitNumWord32 -> pure $ Word32 num'
    LitNumWord64 -> pure $ Word64 num'
    -- TODO: The BigNat primitive operations are kind of "hidden". Somehow, we
    -- want to wrap the behaviour!
    -- LitNumBigNat -> throwError ()
    _ -> throwError UnsupportedExpr
    where
      num' :: Num a => RuntimeValue a
      num' = pure $ fromInteger num

  LitFloat num -> do
    let num' = pure $ fromRational num
    pure $ Float num'

  LitDouble num -> do
    let num' = pure $ fromRational num
    pure $ Double num'

  _ -> throwError UnsupportedExpr
