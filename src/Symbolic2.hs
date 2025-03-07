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

import Grisette hiding (PPrintType (..))
import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Map.Expr (TrieMap(..), insertTM)
import GHC.Types.Unique.DFM (UniqDFM)
import GHC.Platform (Platform (platformWordSize))
import GHC.Generics (Generic)
import GHC.Builtin.PrimOps (PrimOp (..))
import GHC.MonadCore
import GHC.TypeLits (KnownNat, type (<=), OrderingI (..))
import GHC.TypeNats (cmpNat)

import Control.Monad.Except

-- import Data.Word (Word64)
import Data.Data (type (:~:) (..), Proxy (..))
import Data.Type.Ord (Compare)

import Unsafe.Coerce (unsafeCoerce)
import Control.Monad (forM, foldM)
import GHC.Tc.Utils.TcType (eqType)
import GHC.Builtin.Types.Prim
import Grisette.Lib.Control.Monad.Except (mrgModifyError)
import Control.Exception (ArithException)
import Data.String (IsString(..))
import Control.Monad.State
import GHC.Core.TyCo.Rep (scaledThing)
-- TODO: If we don't end up needing all these imports, we should remove some
-- of the packages we used for this from the package list (though they were only
-- made visible really).
-- import Grisette.Internal.SymPrim.Prim.Internal.Term (Term, LinkedRep (..), SupportedPrim (..))
-- import Grisette.Internal.SymPrim.Prim.Term (SupportedPrimConstraint, SBVRep (..), conTerm, symTerm, SupportedNonFuncPrim (..), NonFuncSBVRep (..), pevalITEBasicTerm, pevalDefaultEqTerm, pevalNotTerm, distinctTerm)
-- import qualified Data.SBV as SBV
-- import Data.SBV (SBV, HasKind, SymVal)
-- import Language.Haskell.TH.Syntax (Lift)

-- import Control.DeepSeq (NFData)
-- import Data.Hashable (Hashable)
-- import Data.String (IsString (..))
-- import Grisette.Internal.SymPrim.Prim.Internal.Term (Term(..))
-- import Data.Foldable (toList)
-- import Data.List.NonEmpty (NonEmpty (..))

testSymbolic
  :: MonadCore m
  => HasDynFlags m
  => MonadFail m
  => CoreExpr
  -> m ()
testSymbolic expr = do
  dflags <- getDynFlags
  let _wordSize = platformWordSize $ targetPlatform dflags
  -- let config = Config
  --       { wordSize = toWordSize . platformWordSize $ targetPlatform dflags
  --       }

  let s = SymbolicState
        { nextADT = 0
        }
  -- value <- case intToIntFun @_ @64 expr of
  --   Right value -> pure value
  --   _ -> fail "No int to int function"
  symbolic <- flip evalStateT s $ runExceptT $ saturated @_ @64 expr >>= asADT
  value <- case symbolic of
    Right value -> pure value
    Left err -> fail $ "Error creating symbolic version: " <> show err

  dbg' $ show value

  let z3' = z3
        { sbvConfig = (sbvConfig z3)
          { verbose = True
          }
        }


  liftCore . liftIO $ do
    -- let f = sym "0" :: ADT -~> ADT
    let g = sym "0" :: ADT -~> SymIntN64
    -- result <- solve z3' $ (fmap ((g #) . (f #)) value) .== pure (0x10)
    let translate = \case
          -- Right val -> g # (f # val) .== 0x10
          Right val -> g # val .== 0x10
          -- TODO: I guess we want to handle Invalid differently from the other
          -- errors?
          Left _ -> false

    result <- solveExcept z3' translate value
    -- result <- solve z3' $ value .== throwError DivideByZero
    -- let x = sym "x" :: SymIntN64
    -- let f = sym "0" :: SymIntN64 -~> SymIntN64
    -- let f' = sym "0" :: SymIntN32 -~> SymIntN64
    -- result <- solve z3' $ f # x ./= f' # fromInteger 0
    print result

asIntN64 :: MonadError SymbolicError m => Value n -> m (RuntimeValue SymIntN64)
asIntN64 = \case
  Int64 value -> pure value
  _ -> throwError IllTyped

asADT :: MonadError SymbolicError m => Value n -> m (RuntimeValue SymIntN64)
asADT = \case
  ADT value -> pure value
  _ -> throwError IllTyped

saturated
  :: MonadSymbolic m
  => KnownPos n
  => CoreExpr
  -> m (Value n)
saturated expr = do
  symbolic <- eval emptyTM expr
  let (bndrs, _) = collectBinders expr
  symBndrs <- forM bndrs $ \bndr -> do
    symBndr <- symbolicInstance bndr
    pure $ Val symBndr
  saturate symBndrs symbolic

saturate
  :: MonadError SymbolicError m
  => KnownPos n
  => [Symbolic m n]
  -> Symbolic m n
  -> m (Value n)
saturate (arg:args) (Fun fun) = do
  result <- fun arg
  saturate args result 
saturate [] (Val val) = pure val
saturate _ _ = throwError IllTyped

symbolicInstance
  :: MonadError SymbolicError m
  => KnownPos n
  => Id
  -> m (Value n)
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
  deriving SymEq via (Default RuntimeError)

type RuntimeValue a = ExceptT RuntimeError Union a

type ADT = SymIntN64

type KnownPos n = (KnownNat n, 1 <= n)

data SymbolicError where
  IllTyped :: SymbolicError
  UnsupportedExpr :: SymbolicError
  UnboundVariable :: SymbolicError
  deriving Show

data Value n where
  -- Char :: RuntimeValue (SymWordN 31) -> Value n
  -- BigNat :: RuntimeValue SymInteger -> Value n
  Int :: RuntimeValue (SymIntN n) -> Value n
  Int8 :: RuntimeValue SymIntN8 -> Value n
  Int16 :: RuntimeValue SymIntN16 -> Value n
  Int32 :: RuntimeValue SymIntN32 -> Value n
  Int64 :: RuntimeValue SymIntN64 -> Value n
  Word :: RuntimeValue (SymWordN n) -> Value n
  Word8 :: RuntimeValue SymWordN8 -> Value n
  Word16 :: RuntimeValue SymWordN16 -> Value n
  Word32 :: RuntimeValue SymWordN32 -> Value n
  Word64 :: RuntimeValue SymWordN64 -> Value n
  Float :: RuntimeValue SymFP32 -> Value n
  Double :: RuntimeValue SymFP64 -> Value n
  -- TODO: Do we not maybe want to attach a Type to this?
  ADT :: RuntimeValue ADT -> Value n
  Ty :: Type -> Value n

-- TODO: Somehow this split feels somewhat unnatural. I think it would be better
-- to have Fun be part of Value. A giveaway here is that there is no sensible
-- name for this type. It is, in fact, also a value. Maybe we could do like a
-- 'Prim n' thing for all primitive values. Then ADT, Ty And Fun can be part of
-- value.
data Symbolic m n where
  Val :: Value n -> Symbolic m n
  Fun :: (Symbolic m n -> m (Symbolic m n)) -> Symbolic m n

type MonadSymbolic m = (MonadError SymbolicError m, MonadState SymbolicState m, MonadCore m)

newtype SymbolicState = SymbolicState
  { nextADT :: ADT
  }

freshADT :: MonadState SymbolicState m => m (RuntimeValue ADT)
freshADT = state $ \s -> do
  let adt = nextADT s
  let s' = s { nextADT = adt + 1}
  (pure adt, s')

-- bigNat :: RuntimeValue SymInteger -> Value' n
-- bigNat val = do
--   let conditional = val .>= 0
--   let err = throwError Invalid
--   BigNat' $ mrgIte conditional val err

-- char :: Char -> Value' n
-- char val = do
--   let conditional = val .>= 0
--   let val' = pure $ fromInteger val
--   let err = throwError Invalid
--   BigNat' $ mrgIte conditional val' err

type Environment m n = UniqDFM Var (Symbolic m n)

eval
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => Environment m n
  -> CoreExpr
  -> m (Symbolic m n)
eval env = \case
  Var var | Just op <- isPrimOpId_maybe var -> symPrimOp op
  Var var | Just dataCon <- isDataConId_maybe var -> symDataCon dataCon
  Var var -> whyFail UnboundVariable $ lookupTM var env

  Lit lit -> do
    lit' <- symLiteral lit
    pure $ Val lit'

  Lam bndr body -> pure . Fun $ \arg -> do
    -- TODO: I think it would be good to have a check here to ensure that the
    -- argument has the correct type.
    let env' = insertTM bndr arg env
    eval env' body

  App fun arg -> do
    fun' <- eval env fun
    arg' <- eval env arg
    applySymbolic fun' arg'

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

    scrut'' <- case scrut' of
      Val scrut'' -> pure scrut''
      Fun _ -> throwError IllTyped

    alts' <- forM alts $ symAlt env' scrut''

    final <- invalidSymbolic ty

    foldM' final alts' $ \fl (cond, rhs) -> do
      symBranch cond rhs fl

  -- TODO: I think we can actually do something reasonable here.
  Cast _expr _coercion -> throwError UnsupportedExpr

  -- Ticks do not affect evaluation, thus we can skip it.
  Tick _ expr -> eval env expr

  Type ty -> pure $ Val (Ty ty)

  -- TODO: Should we do anything with this. I think we do, but I'll have to
  -- figure out the normal cast first...
  Coercion _ -> throwError UnsupportedExpr

applySymbolic
  :: MonadError SymbolicError m
  => Symbolic m n
  -> Symbolic m n
  -> m (Symbolic m n)
applySymbolic fun arg = case fun of
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
  -> Value n
  -> CoreAlt
  -> m (RuntimeValue SymBool, Symbolic m n)
symAlt env scrut = \case
  Alt (DataAlt dataCon) bndrs rhs -> do
    -- Ensure the scrutinee is actually an ADT.
    scrut' <- case scrut of
      ADT adt -> pure adt
      _ -> throwError IllTyped

    -- Whether the "tag" field on this ADT is equivalent to the DataCon.
    let conditional = adtIsDataCon scrut' dataCon

    -- Gather field accessors for all binders.
    let names = dataConAccessorNames dataCon
    let accessors = zip names bndrs
    fields <- forM accessors $ \(name, bndr) -> do
      Val <$> accessField scrut' name (varType bndr)

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

  -- FIXME: We should have an Invalid ite for defaults on data-alts, as we do
  -- want to capture the range of alternatives (important for translating it
  -- back to a readable result). I.e. the default should only be constructors
  -- that exists for the given scrutinee.
  Alt DEFAULT [] rhs -> do
    let conditional = pure true
    rhs' <- eval env rhs
    pure (conditional, rhs')

  _ -> throwError UnsupportedExpr

symDataCon
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => DataCon
  -> m (Symbolic m n)
symDataCon dataCon = do
  -- The root creates the actually symbolic DataCon using the given type
  -- instantiation.
  let root = symDataConInst dataCon

  -- The number of type arguments we actually require.
  let nUnivTys = const () <$> dataConUnivTyVars dataCon

  -- Create an n-ary function accepting types, which will be used to instantiate
  -- the data constructor.
  final <- nArity root nUnivTys $ \_ univ -> \case
    Val (Ty ty) -> pure $ ty : univ
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
  -> m (Symbolic m n)
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
        let adt' = ADT $ assertRuntime cond adt
        pure $ Val adt'

  -- Accumulate a function that takes the fields' as arguments. We pass a
  -- conditional to the root that states the field accessors are equal to the
  -- actual arguments.
  final <- nArity root fields $ \field cond arg -> do
    arg' <- case arg of
      Fun _ -> throwError UnsupportedExpr
      Val v -> pure v

    -- Constraint the field of the ADT to be equivalent to the argument.
    extra <- cmpValue field arg'
    pure $ liftA2 (.&&) extra cond

  -- As a final constraint, we constrain the ADT match the given DataCon.
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
  => (b -> m (Symbolic m n))
  -- ^ Root value and what we accumulate.
  -> t a
  -- ^ What we fold over. Decides the arity of the function.
  -> (a -> b -> Symbolic m n -> m b)
  -- ^ Accumulation function
  -> m (b -> m (Symbolic m n))
nArity acc xs f = foldM' acc xs $ \acc' x -> do
  pure $ \y -> pure . Fun $ \arg -> do
    res <- f x y arg
    acc' res

-- | Whether the given ADT matches the DataCon.
--
-- Note, this does not typecheck whether the ADT actually matches the DataCon.
-- TODO: I do want this to perform a typecheck! I would need to include the
-- type on an ADT first.
adtIsDataCon :: RuntimeValue ADT -> DataCon -> RuntimeValue SymBool
adtIsDataCon adt dataCon = do
  tag <- accessTag adt
  let dataCon' = fromIntegral $ dataConTagZ dataCon
  mrgReturn $ tag .== dataCon'

-- | Accessor for the tag of an ADT.
accessTag
  :: RuntimeValue ADT
  -> RuntimeValue SymIntN64
accessTag adt = do
  let tag = "tag" :: ADT -~> SymIntN64
  adt' <- adt
  pure $ tag # adt'

-- | Accessor for a field of an ADT.
--
-- The field is a pair of name and its result type.
accessField
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => RuntimeValue ADT
  -> String
  -> Type
  -> m (Value n)
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
  | Just _ <- tcSplitTyConApp_maybe ty = pure $ ADT construct
  | otherwise = throwError UnsupportedExpr
  where
    construct
      :: forall c t
       . Solvable (IntN64 --> c) (ADT -~> t)
      => RuntimeValue t
    construct = do
      let symbol = simple . identifier . fromString $ name
      let accessor = sym symbol :: ADT -~> t
      scrut' <- adt
      pure $ accessor # scrut'

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
  => Value n
  -> Value n
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
cmpValue (ADT lhs) (ADT rhs) = pure $ cmpRuntime lhs rhs
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
-- TODO: We should make a lazy iteRuntime. This one is useful for case
-- expressions, but not for assertions. Assertions should not force evaluation,
-- but just restrict computation given no failure occurred. Maybe the problem
-- is in the comparison function cmpRuntime btw. I'll have to think about it
-- once I add support for bottom values.
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
-- FIXME: This should respect lazy semantics. The current implementation forces
-- the conditional, which is not what we want from an assert.
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
  -> Value n
  -> Value n
  -> m (Value n)
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
iteValue cond (ADT lhs) (ADT rhs) = pure . ADT $ iteRuntime cond lhs rhs
iteValue _ _ _ = throwError IllTyped

-- | Branch on a symbolic runtime boolean.
symBranch
  :: MonadError SymbolicError m
  => KnownPos n
  => RuntimeValue SymBool
  -> Symbolic m n
  -> Symbolic m n
  -> m (Symbolic m n)
symBranch cond (Fun tr) (Fun fl) = pure . Fun $ \arg -> do
  tr' <- tr arg
  fl' <- fl arg
  symBranch cond tr' fl'
symBranch cond (Val tr) (Val fl) = do
  value <- iteValue cond tr fl
  pure $ Val value
symBranch _ _ _ = throwError IllTyped

-- | A symbolic for statements that cannot be reached.
--
-- It will be typed according to the given core type.
invalidSymbolic
  :: MonadError SymbolicError m
  => KnownPos n
  => Type
  -> m (Symbolic m n)
invalidSymbolic ty = case splitFunTy_maybe ty of
  Just (_, _, _, res) -> pure . Fun $ \_ -> invalidSymbolic res
  _ -> Val <$> invalidValue ty

typedValue
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => (forall c a. Solvable c a => RuntimeValue a)
  -> Type
  -> m (Value n)
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
  | Just _ <- tcSplitTyConApp_maybe ty = pure $ ADT fun
  | otherwise = throwError UnsupportedExpr

-- | A value that should not be reachable.
--
-- It will be typed according to the given core type.
invalidValue 
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => Type
  -> m (Value n)
invalidValue = typedValue $ throwError Invalid

-- | Annotate why there was no result.
whyFail :: MonadError e m => e -> Maybe a -> m a
whyFail err = maybe (throwError err) pure

-- TODO: Add support for all primitive operations.
symPrimOp
  :: forall m n
   . MonadError SymbolicError m
  => PrimOp
  -> m (Symbolic m n)
symPrimOp = \case
  Int64AddOp ->
    pure . Fun $ \case
      Val (Int64 lhs) -> pure . Fun $ \case
        Val (Int64 rhs) -> pure . Val . Int64 $ do
          lhs' <- lhs
          rhs' <- rhs
          mrgReturn $ lhs' + rhs'
        _ -> throwError IllTyped
      _ -> throwError IllTyped
  Int64QuotOp ->
    pure . Fun $ \case
      Val (Int64 lhs) -> pure . Fun $ \case
        Val (Int64 rhs) -> pure . Val . Int64 $ do
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
  -> m (Value n)
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

-- | Symbolic Shift Right Arithmetic.
--
-- This will use a conversion into a signed bitvector, as the symbolic executor
-- does not distinguish between arithmetic and logical shift per type.
symShiftRA
  :: forall bv n i
   . SymFromIntegral (SymIntN n) (bv n)
  => SymFromIntegral (bv n) (SymIntN n)
  => KnownPos n
  => KnownPos i
  => bv n
  -> SymIntN i
  -> bv n
symShiftRA val idx = do
  let idx' = sizedBVResize idx :: SymIntN n
  let idx'' = symFromIntegral idx'

  let val' = symFromIntegral val :: SymIntN n
  -- TODO: Same thing as with symShiftL (i.e. non-total function)
  let result = symShiftNegated val' idx''
  symFromIntegral result

-- | Symbolic Shift Right Logical.
--
-- This will use a conversion into a signed bitvector, as the symbolic executor
-- does not distinguish between arithmetic and logical shift per type.
symShiftRL
  :: forall bv n i
   . SymFromIntegral (SymWordN n) (bv n)
  => SymFromIntegral (bv n) (SymWordN n)
  => KnownPos n
  => KnownPos i
  => bv n
  -> SymIntN i
  -> bv n
symShiftRL val idx = do
  let idx' = sizedBVResize idx :: SymIntN n
  let idx'' = symFromIntegral idx'

  let val' = symFromIntegral val :: SymWordN n
  -- TODO: Same thing as with symShiftL (i.e. non-total function)
  let result = symShiftNegated val' idx''
  symFromIntegral result

-- | Symbolic Shift Left
--
-- Symbolic shifts in Haskell all use the platform-sized int for the index (i.e.
-- the amount to shift by). This function performs the necessary conversions in
-- order to be compatible with the symbolic shift.
symShiftL
  :: forall bv n i
   . SymFromIntegral (SymIntN n) (bv n)
  => SymShift (bv n)
  => KnownPos n
  => KnownPos i
  => bv n
  -> SymIntN i
  -> bv n
symShiftL val idx = do
  let idx' = sizedBVResize idx :: SymIntN n
  let idx'' = symFromIntegral idx'
  -- TODO: Haskell doesn't really define what to do with the shift if the index
  -- is larger than the word size. It is considered unsafe. We should do
  -- something with this? Not sure what exactly that would be though... How
  -- would we ever model UB? Just for comparison btw, the safe version of the
  -- primitive shifts just masks the value to 0 if it excedes the size. Other
  -- implementations (like Word8) actually throw an error...
  --
  -- In any case, they  all do something to wrap the UB into non-UB. There is
  -- no direct way to model the UB I guess... Maybe it is okay to assume that
  -- only safe uses exist? I.e. with non-UB behaviour at the top level. Then it
  -- doens't matter what we do for those  cases anyway, as they're wrapped into
  -- something that is always defined.
  --
  -- One thing we do need to account for is failure. Currently we do not track
  -- failure of functions anywhere, but I guess we techinically should?
  --
  -- Now that I think about it btw, I don't think a shift will ever actually
  -- occur in hardware? Maybe I've been caring slightly too much about them?
  symShift val idx''

-- | Resize the given bitvector.
--
-- Whether the bitvector is sign extended or not depends on its implementation
-- of 'sizedBVExt'.
sizedBVResize
  :: forall bv l r
   . SizedBV bv
  => KnownNat l
  => KnownNat r
  => 1 <= l
  => 1 <= r
  => bv l
  -> bv r
sizedBVResize = case cmpNat (Proxy @l) (Proxy @r) of
  LTI -> sizedBVExt $ Proxy @r
  EQI -> id
  -- SAFETY: The unsafe coerce is just to have 'r <= l' as Haskell cannot figure
  -- this out given the 'l >= r' that is already in context. Theoretically we
  -- should be able to do this without unsafeCoerce, but I'm not sure how.
  -- I'm not keen on importing the type level nat plugin for just one function.
  GTI -> case unsafeCoerce Refl :: (Compare r l :~: 'LT) of
    Refl -> sizedBVSelect (Proxy @0) (Proxy @r)

-- | The usual 'foldM', but with its arguments switched.
--
-- The use for this is that one may use this to write an expression in the
-- following shape:
-- ```
-- res <- foldM' acc xs $ \acc' x -> do
--   ...
-- ```
foldM' :: (Foldable t, Monad m) => b -> t a -> (b -> a -> m b) -> m b
foldM' acc xs f = foldM f acc xs
