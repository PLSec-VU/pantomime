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

module Symbolic2
  ( testSymbolic
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Map.Expr (TrieMap(..), insertTM)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Unify (tcMatchTy)
import GHC.Types.Unique.DFM (UniqDFM)
import GHC.Platform (Platform (platformWordSize))
import GHC.Generics (Generic)
import GHC.Builtin.PrimOps (PrimOp (..))
import GHC.Builtin.Types.Prim
import GHC.Tc.Utils.TcType (eqType, tcSplitSigmaTy, substTy)
import GHC.MonadCore

import Control.Monad (forM, unless)
import Control.Monad.Except
import Control.Monad.State
import Control.Exception (ArithException)

import Data.Foldable (find, forM_)
import Data.String (IsString(..))
import Data.Functor ((<&>))

-- TODO: There has to be a better way to not import pretty printing stuff from
-- grisette...
import Grisette hiding (PPrintType (..), (<>), (<+>), nest, punctuate, comma, vcat, braces, lbrace, rbrace)
import Grisette.Lib.Control.Monad.Except (mrgModifyError)
import Grisette.Internal.SymPrim.Prim.Term (ModelValue (..))

import SymUtil

-- TODO: Importantant things to do right now
-- - 'Symbolic' and 'Value' kind of feel like they should be merged. We should
-- just have one 'Value' data type.
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
        { nextADT = 0
        }

  symbolic <- flip evalStateT s $ runExceptT $ do
    (bndrs, result) <- saturated @_ @64 expr 
    result' <- asADT result
    pure (bndrs, result')

  (args, value) <- case symbolic of
    Right (bndrs, value) -> pure (bndrs, value)
    Left err -> fail $ "Error creating symbolic version: " ++ show err

  forM_ args $ \case
    Cast' co _ -> dbg co
    ADT ty _ -> dbg ty
    _ -> dbg' "whut?"

  dbg' $ show value

  let z3' = z3
        { sbvConfig = (sbvConfig z3)
          { verbose = True
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

-- TODO: I think this is not the cleanest representation. We should make this
-- a bit better.
data ModelValue' where
  Record :: DataCon -> [(String, ModelValue')] -> ModelValue'
  Primitive :: ModelValue -> ModelValue'
  Error :: RuntimeError -> ModelValue'
  -- TODO: We want to give out Unknown for recursive values. I guess we'll leave
  -- this for now...
  -- Unknown :: ModelValue'

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
    Error err -> ppr err

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
  ADT ty adt -> case evalSymToCon @_ @(Either RuntimeError ADT) model adt of
    Right adt' -> do
      let x = do
            (tyCon, _) <- splitTyConApp_maybe ty
            tyConDataCons_maybe tyCon
      dbg' "==========="
      dbg ty
      dbg x
      let tag = evalSymToCon @_ @Tag model $ accessTag adt'
      -- TODO: I guess this could also just mean that the value is irrelevant
      -- no? This perhaps should return Unknown on failure.
      dataCon <- whyFail IllTyped $ tagToDataCon tag ty
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

    Left err -> pure $ Error err

  -- TODO: I don't think this is a nice way to implement this...
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
  Fun _ _ -> throwError IllTyped
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
  deriving Mergeable via (Default RuntimeError)
  deriving EvalSym via (Default RuntimeError)
  deriving SymEq via (Default RuntimeError)

instance Outputable RuntimeError where
  ppr = \case
    DivideByZero -> text "divide-by-zero"
    Invalid -> text "invalid"

type RuntimeValue a = ExceptT RuntimeError Union a

type ADT = SymIntN64

-- | ADT tag to distinguish between constructors.
type Tag = SymWordN64

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
  Fun :: Kind -> (Value m n -> m (Value m n)) -> Value m n
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
  { nextADT :: ADT
  }

freshADT :: MonadState SymbolicState m => m (RuntimeValue ADT)
freshADT = state $ \s -> do
  let adt = nextADT s
  let s' = s { nextADT = adt + 1}
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

  Lam bndr body -> pure . Fun (varType bndr) $ \arg -> do
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
  Fun _ty fun' -> do
    -- Ensure the types match up.
    -- let ty' = valueType arg
    -- unless (ty `eqType` ty') $ throwError IllTyped

    -- Run the inner function.
    fun' arg
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
    let conditional = adtIsDataCon scrut' dataCon

    -- Gather field accessors for all binders.
    let names = dataConAccessorNames dataCon
    let accessors = zip names bndrs
    fields <- forM accessors $ \(name, bndr) -> do
      accessField scrut' name (varType bndr)

    -- Extend the environment with field accessors for each binder.
    let env' = foldl' (flip $ uncurry insertTM) env $ zip bndrs fields

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
            tag <- accessTag <$> adt
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

  -- Accumulate a function that takes the fields' as arguments. We pass a
  -- conditional to the root that states the field accessors are equal to the
  -- actual arguments.
  final <- nArity root fields $ \field cond arg -> do
    -- Constraint the field of the ADT to be equivalent to the argument.
    extra <- cmpValue field arg
    pure $ liftA2 (.&&) extra cond

  -- As a final constraint, the ADT tag should match the given DataCon.
  final $ adtIsDataCon adt dataCon

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
  pure $ \y -> pure . Fun undefined $ \arg -> do
    res <- f x y arg
    acc' res

-- | Get the DataCon from the Tag and Type.
tagToDataCon
  :: Tag
  -> Type
  -> Maybe DataCon
tagToDataCon tag ty = do
  (tyCon, _) <- splitTyConApp_maybe ty
  dataCons <- tyConDataCons_maybe tyCon
  let cmp dataCon = dataConToTag dataCon == tag
  find cmp dataCons

-- | Get the symbolic representation of the DataCon.
dataConToTag :: DataCon -> Tag
dataConToTag = fromIntegral . dataConTagZ

-- | Whether the given ADT matches the DataCon.
--
-- Note, this does not typecheck whether the ADT actually matches the DataCon.
-- TODO: I do want this to perform a typecheck! I would need to include the
-- type on an ADT first.
adtIsDataCon
  :: RuntimeValue ADT
  -> DataCon
  -> RuntimeValue SymBool
adtIsDataCon adt dataCon = do
  field <- accessTag <$> adt
  let tag = dataConToTag dataCon
  mrgReturn $ field .== tag

-- | Accessor for the tag of an ADT.
accessTag
  :: ADT
  -> Tag
accessTag adt = do
  let tag = "tag" :: ADT -~> Tag
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
  | Just _ <- tcSplitTyConApp_maybe ty = pure $ ADT ty construct
  | otherwise = throwError UnsupportedExpr
  where
    construct
      :: forall c t
       . Solvable (IntN64 --> c) (ADT -~> t)
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
iteValue cond (Fun lty lhs) (Fun rty rhs) = do
  unless (lty `eqType` rty) $ throwError IllTyped
  pure . Fun lty $ \arg -> do
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
  Fun _ty _ -> undefined
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
typedValue fun ty
  | ty `eqType` intPrimTy = pure $ Int fun
  | ty `eqType` int8PrimTy = pure $ Int8 fun
  | ty `eqType` int16PrimTy = pure $ Int16 fun
  | ty `eqType` int32PrimTy = pure $ Int32 fun
  | ty `eqType` int64PrimTy = pure $ Int64 fun
  | ty `eqType` wordPrimTy = pure $ Word fun
  | ty `eqType` word8PrimTy = pure $ Word8 fun
  | ty `eqType` word16PrimTy = pure $ Word16 fun
  | ty `eqType` word32PrimTy = pure $ Word32 fun
  | ty `eqType` word64PrimTy = pure $ Word64 fun
  | ty `eqType` floatPrimTy = pure $ Float fun
  | ty `eqType` doublePrimTy = pure $ Double fun
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (ty', co) <- instNewTyCon_maybe tyCon tys = do
    value <- typedValue fun ty'
    let co' = mkSymCo co
    pure $ mkCast' co' value
  | Just _ <- tcSplitTyConApp_maybe ty = pure $ ADT ty fun
  | Just (_, _, _, res) <- splitFunTy_maybe ty = do
    let fun' _ = typedValue fun res
    pure $ Fun ty fun'
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

-- TODO: Add support for all primitive operations.
symPrimOp
  :: forall m n
   . MonadError SymbolicError m
  => PrimOp
  -> m (Value m n)
symPrimOp = \case
  Int64AddOp ->
    pure . Fun int64PrimTy $ \case
      Int64 lhs -> pure . Fun int64PrimTy $ \case
        Int64 rhs -> pure . Int64 $ do
          lhs' <- lhs
          rhs' <- rhs
          mrgReturn $ lhs' + rhs'
        _ -> throwError IllTyped
      _ -> throwError IllTyped
  Int64QuotOp ->
    pure . Fun int64PrimTy $ \case
      Int64 lhs -> pure . Fun int64PrimTy $ \case
        Int64 rhs -> pure . Int64 $ do
          lhs' <- lhs
          rhs' <- rhs
          mrgModifyError (const DivideByZero) $ do
            safeQuot @ArithException lhs' rhs'
        _ -> throwError IllTyped
      _ -> throwError IllTyped
  _ -> throwError UnsupportedExpr

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
