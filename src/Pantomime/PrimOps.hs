{-# LANGUAGE PatternSynonyms #-}

module Pantomime.PrimOps
  -- | System Fc operations.
  ( PrimOp
  , ite
  , tagToEnum
  , dataToTag
  , raise
  , unsafeEqualityProof

  -- | Boolean operations.
  , true
  , false
  , not
  , implies
  , and
  , or
  , iff
  , xor

  -- | Integer operations.
  , i2bv
  , ineg
  , iabs
  , iadd
  , imul
  , idiv
  , imod
  , ieq
  , ineq
  , ile
  , ilt

  -- | Bitvector primitive operations.
  , bvu2i
  , bvs2i
  , bvsize'
  , bvnot
  , bvneg
  , bvand
  , bvor
  , bvxor
  , bvadd
  , bvmul
  , bvudiv
  , bvsdiv
  , bvurem
  , bvsrem
  , bvshl
  , bvlshr
  , bvashr
  , bveq
  , bvneq
  , bvule
  , bvsle
  , bvult
  , bvslt
  , bvconcat
  , bvzext
  , bvsext
  , bvselect

  -- | Array primitive operations.
  , aconst
  , aselect
  , astore
  , aeq
  ) where

import Data.Bits (Bits((.&.), (.|.), complement))
import Data.Bits qualified as Bits (xor)
import Data.Constraint (Dict (..))
import Data.Constraint.Unsafe (unsafeAxiom)
import Data.Typeable (type (:~:) (..), eqT, Proxy (..))

import Effectful (type (:>))
import Effectful.Context (Context, ContextMode(..))
import Effectful.Error.Static (HasCallStack, Error)

import GHC.Core.FamInstEnv (FamInstEnvs)
import GHC.Core.TyCo.Rep (UnivCoProvenance(..))
import GHC.Plugins (Role (..), emptySubst, dataConTagZ, mkUnivCo)
import GHC.Utils.Outputable (SDoc, text)
import GHC.TypeLits (type (<=), SomeNat (..), natVal, pattern SNat)

import Grisette
  ( SymIntN
  , SymBool
  , SymInteger
  , SizedBV (..)
  , SymShift (..)
  , SignConversion (..)
  , SymEq (..)
  , SymOrd (..)
  , SymFromIntegral (..)
  , LogicalOp (symNot, symImplies, (.&&), (.||))
  , SimpleMergeable (..)
  , BitCast (..)
  )
import Grisette qualified (LogicalOp (true, false))
import Grisette.Internal.SymPrim.SymArray qualified as Array

import Pantomime.Embed
import Pantomime.Expr
  ( Expr (..)
  , Constructor (..)
  , Eval
  , Runtime
  , collectArgs
  , mkLit
  , mkEnumCon
  , mkRaise
  , failWithE
  , throwE
  , hoistEff
  , deferE
  )
import Pantomime.Literal
  ( BuiltInTyCon
  , SomeLiteralType (..)
  , Literal (..)
  , LiteralTypeable (..)
  , HasDict (..)
  , eqLiteralType
  )
import Pantomime.Util
  ( SomeBitVec (..)
  , KnownPos
  , SymBitVec
  , posNat
  , leqNat
  , (%+)
  )
import Pantomime.Defer (Deferrable, Defer (..))
import Prelude
  ( Applicative (..)
  , Monad (..)
  , Num (..)
  , Integral (..)
  , Maybe (..)
  , String
  , type (~)
  , ($)
  , (<$>)
  , (.)
  , fst
  , fromIntegral
  , id
  )

-- TODO: It might make sense to expose equality (and especially 'distinct') as
-- an operation over a list of elements. Probably we first want to support
-- sequences if we plan on doing this? In any case, this might be useful to
-- expose at some point. For now, we'll leave it as is.

-- TODO: We should implement some conversion operations. Specifically conversion
-- between bitvec and integer is important. Not sure if there are others? Maybe
-- real numbers once we support them?

type PrimOp es
  =  HasCallStack
  => Deferrable es
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => Eval es Expr

-- TODO: This one cannot be declared in Haskell... It can with BoxedRep, but
-- still a definition is not possible.
-- :: forall r (a :: TYPE r). Bool -> r -> r -> r
type ITEOp
  =   Forall 1 TypeKind
  :.  BoolTy
  :-> TyVar 1 (TyVar 0 RuntimeRepTy)
  :-> TyVar 1 (TyVar 0 RuntimeRepTy)
  :-> TyVar 1 (TyVar 0 RuntimeRepTy)

ite :: PrimOp es
ite = embed2 @ITEOp \_ scrut tr fl -> hoistEff do
  scrut' <- scrut
  mrgIte scrut' tr fl

-- TODO: I guess the size of the bitvector is dependent on the platform size.
-- Not sure how to handle this, but for now I'll settle with just using 64-bit.
-- | forall a. BitVec 64 -> a
type TagToEnumOp
  =   Forall 0 TypeKind
  :.  BitVecTy (Natural 64)
  :-> TyVar 0 TypeKind

tagToEnum :: PrimOp es
tagToEnum = embed2 @TagToEnumOp \ty bvE -> do
  SomeBitVec @n bv <- hoistEff bvE
  Refl <- failWithE "tagToEnum: expected 64-bit bitvector" $ eqT @n @64
  -- TODO: I'm not sure how this interacts with the whole type normalisation.
  -- I don't think this is correct. Maybe we should reduce the type first? I
  -- guess we could also opt to do this within the embedding. This one is likely
  -- just faulty. My hunch for now would be to normalise the given type. This
  -- would be in line with the remaining parts that are also normalised.
  -- BTW, I wonder if we need to handle newtypes here? Maybe this would require
  -- some Representational reduction?
  mkEnumCon bv ty

-- TODO: Perhaps we should move this typeclass and the 'embed2' function to the
-- 'Embed' module, as it actually replaces much of what is defined there!
class Wrap a where
  type Wrapped a
  wrap :: a -> Wrapped a 

instance Wrap (Runtime a) where
  type Wrapped (Runtime a) = Runtime a
  wrap = id

instance Wrap b => Wrap (a -> b) where
  type Wrapped (a -> b) = Runtime (a -> Wrapped b)
  wrap f = pure $ wrap . f

embed2
  :: forall ty es a
   . HasCallStack
  => Reflect ty
  => Wrapped (Deferred a) ~ Runtime (Repr ty)
  => Defer es a
  => Wrap (Deferred a)
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => a
  -> Eval es Expr
embed2 x = do
  y <- deferE x
  embed @ty emptySubst $ wrap y

-- forall (l :: Levity) (a :: TYPE (Boxed l)). l -> Int#
type DataToTagOp
  =   Forall 0 LevityTy
  :.  Forall 1 (BoxedRep (TyVar 0 LevityTy))
  :.  TyVar 1 (BoxedRep (TyVar 0 LevityTy))
  :-> BitVecTy (Natural 64)

dataToTag :: PrimOp es
dataToTag = embed2 @DataToTagOp \_ _ valueE -> do
  value <- hoistEff valueE
  -- TODO: Maybe we should make the conversion a function inside of
  -- Pantomime.Expr? It feels a bit odd here.
  case fst $ collectArgs value of
    Con (DataCon dc) -> pure $ SomeBitVec @64 (fromIntegral $ dataConTagZ dc)
    Con (EnumCon @n tag _) | Just Refl <- eqT @n @64 -> pure $ SomeBitVec tag
    _ -> throwE "dataToTag: expected a DataCon or EnumCon constructor"

type RaiseOp
  =   Forall 0 LevityTy
  :.  Forall 1 RuntimeRepTy
  :.  Forall 2 (TYPE (BoxedRep (TyVar 0 LevityTy)))
  :.  Forall 3 (TYPE (TyVar 1 RuntimeRepTy))
  :.  TyVar 2 (TYPE (BoxedRep (TyVar 0 LevityTy)))
  :-> TyVar 3 (TYPE (TyVar 1 RuntimeRepTy))

raise :: PrimOp es
raise = embed2 @RaiseOp \_ _ _ _ err -> mkRaise err

type UnsafeEqualityProofOp
  =   Forall 0 TypeKind
  :.  Forall 1 (TyVar 0 TypeKind)
  :.  Forall 2 (TyVar 0 TypeKind)
  :.  UnsafeEqualityTy
        (TyVar 0 TypeKind)
        (TyVar 1 (TyVar 0 TypeKind))
        (TyVar 2 (TyVar 0 TypeKind))

unsafeEqualityProof :: forall es. PrimOp es
unsafeEqualityProof = embed2 @UnsafeEqualityProofOp \_ tyL tyR -> do
  let prov = PluginProv "pantomime embedded 'unsafeEqualityProof'"
  pure @(Eval es) $ mkUnivCo prov [] Nominal tyR tyL

true :: forall es. PrimOp es
true = embed2 @BoolTy $ pure @(Eval es) Grisette.true

false :: forall es. PrimOp es
false = embed2 @BoolTy $ pure @(Eval es) Grisette.false

not :: PrimOp es
not = embed2 @(BoolTy :-> BoolTy) \value -> do
  symNot <$> hoistEff value

boolbinary
  :: HasCallStack
  => Deferrable es
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => (SymBool -> SymBool -> SymBool)
  -> Eval es Expr
boolbinary f = embed2 @(BoolTy :-> BoolTy :-> BoolTy) \lhs rhs -> do
  lhs' <- hoistEff lhs
  rhs' <- hoistEff rhs
  pure $ f lhs' rhs'

implies :: PrimOp es
implies = boolbinary symImplies

and :: PrimOp es
and = boolbinary (.&&)

or :: PrimOp es
or = boolbinary (.||)

iff :: PrimOp es
iff = boolbinary (.==)

xor :: PrimOp es
xor = boolbinary (./=)

type IntegerBitVecOp
  =    Forall 0 NaturalTy
  :.   KnownNatTy (TyVar 0 NaturalTy)
  :->  (Natural 1 :<= TyVar 0 NaturalTy)
  :->  IntegerTy
  :->  BitVecTy (TyVar 0 NaturalTy)

i2bv :: PrimOp es
i2bv = embed2 @IntegerBitVecOp \_ n _ i -> do
  SomeNat @n _ <- hoistEff n
  Dict <- failWithE "i2bv: expected a positive Nat" $ posNat @n
  i' <- hoistEff i
  pure $ SomeBitVec @n (symFromIntegral i')

ineg :: PrimOp es
ineg = embed2 @(IntegerTy :-> IntegerTy) \value -> do
  negate <$> hoistEff value

iabs :: PrimOp es
iabs = embed2 @(IntegerTy :-> IntegerTy) \value -> do
  abs <$> hoistEff value

ibinary
  :: HasCallStack
  => Deferrable es
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => (SymInteger -> SymInteger -> SymInteger)
  -> Eval es Expr
ibinary f = embed2 @(IntegerTy :-> IntegerTy :-> IntegerTy) \lhs rhs -> do
  lhs' <- hoistEff lhs
  rhs' <- hoistEff rhs
  pure $ f lhs' rhs'

iadd :: PrimOp es
iadd = ibinary (+)

imul :: PrimOp es
imul = ibinary (*)

idiv :: PrimOp es
idiv = ibinary div

imod :: PrimOp es
imod = ibinary mod

icompare
  :: HasCallStack
  => Deferrable es
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => (SymInteger -> SymInteger -> SymBool)
  -> Eval es Expr
icompare f = embed2 @(IntegerTy :-> IntegerTy :-> BoolTy) \lhs rhs -> do
  lhs' <- hoistEff lhs
  rhs' <- hoistEff rhs
  pure $ f lhs' rhs'

ieq :: PrimOp es
ieq = icompare (.==)

ineq :: PrimOp es
ineq = icompare (./=)

ile :: PrimOp es
ile = icompare (.<=)

ilt :: PrimOp es
ilt = icompare (.<)

type BitVecIntegerOp
  =   Forall 0 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> IntegerTy

bvu2i :: PrimOp es
bvu2i = embed2 @BitVecIntegerOp \_n bv -> hoistEff do
  SomeBitVec bv' <- bv
  pure $ symFromIntegral bv'

bvs2i :: PrimOp es
bvs2i = embed2 @BitVecIntegerOp \_n bv -> hoistEff do
  SomeBitVec @n bv' <- bv
  pure $ symFromIntegral (bitCast @_ @(SymIntN n) bv')

bvsize' :: PrimOp es
bvsize' = embed2 @BitVecIntegerOp \_n bv -> hoistEff do
  SomeBitVec @n _ <- bv
  pure $ fromInteger (natVal @n Proxy)

type UnBitVecOp
  =   Forall 0 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)

bvunary
  :: HasCallStack
  => Deferrable es
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => (forall n. KnownPos n => SymBitVec n -> SymBitVec n)
  -> Eval es Expr
bvunary f = embed2 @UnBitVecOp \_n bv -> hoistEff do
  SomeBitVec bv' <- bv
  pure $ SomeBitVec (f bv')

-- | Bitvector bitwise complement.
bvnot :: PrimOp es
bvnot = bvunary complement

-- | Bitvector negation.
bvneg :: PrimOp es
bvneg = bvunary negate

type BinBitVecOp
  =   Forall 0 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)

bvbinary
  :: HasCallStack
  => Deferrable es
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => (forall n. KnownPos n => SymBitVec n -> SymBitVec n -> SymBitVec n)
  -> Eval es Expr
bvbinary f = embed2 @BinBitVecOp \_n lhs rhs -> do
  SomeBitVec @nl lhs' <- hoistEff lhs
  SomeBitVec @nr rhs' <- hoistEff rhs
  Refl <- failWithE "Bitvector binary operation: width mismatch" $ eqT @nl @nr
  pure $ SomeBitVec (f lhs' rhs')

asSignedBin
  :: (KnownPos n => SymIntN n -> SymIntN n -> SymIntN n)
  -> (KnownPos n => SymBitVec n -> SymBitVec n -> SymBitVec n)
asSignedBin f lhs rhs = do
  let lhs' = toSigned lhs
  let rhs' = toSigned rhs
  toUnsigned $ f lhs' rhs'

-- | Bitvector bitwise and.
bvand :: PrimOp es
bvand = bvbinary (.&.)

-- | Bitvector bitwise or.
bvor :: PrimOp es
bvor = bvbinary (.|.)

-- | Bitvector bitwise exclusive or.
bvxor :: PrimOp es
bvxor = bvbinary Bits.xor

-- | Bitvector addition.
bvadd :: PrimOp es
bvadd = bvbinary (+)

-- | Bitvector multiplication.
bvmul :: PrimOp es
bvmul = bvbinary (*)

-- | Bitvector unsigned division.
bvudiv :: PrimOp es
bvudiv = bvbinary div

-- | Bitvector signed division.
bvsdiv :: PrimOp es
bvsdiv = bvbinary $ asSignedBin div
  
-- | Bitvector unsigned remainder.
bvurem :: PrimOp es
bvurem = bvbinary rem

-- | Bitvector signed remainder.
bvsrem :: PrimOp es
bvsrem = bvbinary $ asSignedBin rem

-- | Bitvector shift left.
bvshl :: PrimOp es
bvshl = bvbinary symShift

-- | Bitvector logical shift right.
bvlshr :: PrimOp es
bvlshr = bvbinary symShiftNegated

-- | Bitvector arithmetic shift right.
bvashr :: PrimOp es
bvashr = bvbinary $ asSignedBin symShiftNegated

-- -- TODO: both bvrol and bvror are parametric over the shift amount more akin to
-- -- KnownNat. Perhaps it would be best to model them as such? This is also more
-- -- transparent to the user! I'll have to first maybe see what code exactly is
-- -- emitted by grisette when I want to do this in the first place.
-- bvrol :: PrimOpExpr es
-- bvrol = undefined

-- bvror :: PrimOpExpr es
-- bvror = undefined

type CompareBitVecOp
  =   Forall 0 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)
  :-> BoolTy

bvcompare
  :: HasCallStack
  => Deferrable es
  => Error String :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FamInstEnvs :> es
  => (forall n. KnownPos n => SymBitVec n -> SymBitVec n -> SymBool)
  -> Eval es Expr
bvcompare f = embed2 @CompareBitVecOp \_ lhs rhs -> do
  SomeBitVec @nl lhs' <- hoistEff lhs
  SomeBitVec @nr rhs' <- hoistEff rhs
  Refl <- failWithE "Bitvector comparison: width mismatch" $ eqT @nl @nr
  pure $ f lhs' rhs'

asSignedCmp
  :: (KnownPos n => SymIntN n -> SymIntN n -> SymBool)
  -> (KnownPos n => SymBitVec n -> SymBitVec n -> SymBool)
asSignedCmp f lhs rhs = do
  let lhs' = toSigned lhs
  let rhs' = toSigned rhs
  f lhs' rhs'

bveq :: PrimOp es
bveq = bvcompare (.==)

bvneq :: PrimOp es
bvneq = bvcompare (./=)

bvule :: PrimOp es
bvule = bvcompare (.<=)

bvsle :: PrimOp es
bvsle = bvcompare $ asSignedCmp (.<=)

bvult :: PrimOp es
bvult = bvcompare (.<)

bvslt :: PrimOp es
bvslt = bvcompare $ asSignedCmp (.<)

type ConcatBitVecOp
  =   Forall 0 NaturalTy
  :.  Forall 1 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 1 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy :+ TyVar 1 NaturalTy)

bvconcat :: PrimOp es
bvconcat = embed2 @ConcatBitVecOp \_ _ lhs rhs -> hoistEff do
  SomeBitVec @nl lhs' <- lhs
  SomeBitVec @nr rhs' <- rhs
  SNat @n <- pure $ SNat @nl %+ SNat @nr
  -- SAFETY: Both bitvectors already have a positive bitwidth, thus their
  -- concatenation also has a positive bitwidth.
  Dict <- pure $ unsafeAxiom @(1 <= n)
  pure $ SomeBitVec (sizedBVConcat lhs' rhs')

-- forall l r. KnownNat r => l <= r => BitVec l -> BitVec r
type ExtendBitVecOp
  =   Forall 0 NaturalTy
  :.  Forall 1 NaturalTy
  :.  KnownNatTy (TyVar 1 NaturalTy)
  :-> (TyVar 0 NaturalTy :<= TyVar 1 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 1 NaturalTy)

bvextend
  :: ( forall l r
     . KnownPos l
    => KnownPos r
    => l <= r
    => Proxy r
    -> SymBitVec l
    -> SymBitVec r
     )
  -> PrimOp es
bvextend f = embed2 @ExtendBitVecOp \_ _ r _ bv -> do
  SomeBitVec @l bv' <- hoistEff bv
  SomeNat @r _ <- hoistEff r
  Dict <- failWithE "Bitvector extend: size constraint violation (l <= r)" $ leqNat @l @r
  Dict <- failWithE "Bitvector extend: expected positive result size" $ posNat @r
  pure $ SomeBitVec (f (Proxy @r) bv')

bvzext :: PrimOp es
bvzext = bvextend sizedBVZext

bvsext :: PrimOp es
bvsext = bvextend sizedBVSext

-- :: forall idx width n
--  . KnownNat idx
-- => KnownNat width
-- => 1 <= width
-- => idx + width <= n
-- => BitVec n
-- -> BitVec width
type SelectBitVecOp
  =   Forall 0 NaturalTy
  :.  Forall 1 NaturalTy
  :.  Forall 2 NaturalTy
  :.  KnownNatTy (TyVar 0 NaturalTy)
  :-> KnownNatTy (TyVar 1 NaturalTy)
  :-> (Natural 1 :<= TyVar 1 NaturalTy)
  :-> (TyVar 0 NaturalTy :+ TyVar 1 NaturalTy :<= TyVar 2 NaturalTy)
  :-> BitVecTy (TyVar 2 NaturalTy)
  :-> BitVecTy (TyVar 1 NaturalTy)

bvselect :: PrimOp es
bvselect = embed2 @SelectBitVecOp \_ _ _ idx width _ _  bv -> do
  SomeNat @idx _ <- hoistEff idx
  SomeNat @width _ <- hoistEff width
  SomeBitVec @n bv' <- hoistEff bv
  Dict <- failWithE "Bitvector select: expected positive width" $ posNat @width
  SNat @sum <- pure $ SNat @idx %+ SNat @width
  Dict <- failWithE "Bitvector select: index+width exceeds bitvector size" $ leqNat @sum @n
  pure $ SomeBitVec (sizedBVSelect (Proxy @idx) (Proxy @width) bv')

-- :: forall k v. Primitive k => Primitive v => v -> Array k v
type ArrayConstOp
  =   Forall 0 TypeKind
  :.  Forall 1 TypeKind
  :.  PrimitiveTy (TyVar 0 TypeKind)
  :-> PrimitiveTy (TyVar 1 TypeKind)
  :-> TyVar 1 TypeKind
  :-> ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)

aconst :: PrimOp es
aconst = embed2 @ArrayConstOp \_ _ pk _ valE -> do
  -- Gather constraints for primitive types.
  (_kco, SomeLiteralType @k kty) <- hoistEff pk

  -- Gather the literal, knowing it is one due to the constraint.
  Literal @v vty val <- hoistEff valE >>= \case
    Lit lit -> pure lit
    _ -> throwE "aconst: expected a literal value"

  -- Gather evidence required to perform the array operation.
  Dict <- pure $ evidence kty
  Dict <- pure $ evidence vty

  -- Create the constant array.
  let array = Array.const @k @v val
  pure $ SomeArray array

-- :: forall k v. Primitive k => Primitive v => Array k v -> k -> v
type ArraySelectOp
  =   Forall 0 TypeKind
  :.  Forall 1 TypeKind
  :.  ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)
  :-> TyVar 0 TypeKind
  :-> TyVar 1 TypeKind

aselect :: PrimOp es
aselect = embed2 @ArraySelectOp \_ _ arrE keyE -> do
  -- Get the inner array.
  SomeArray @k @v arr <- hoistEff arrE

  -- Gather the literal, knowing it is one due to the constraint.
  Literal kty key <- hoistEff keyE >>= \case
    Lit lit -> pure lit
    _ -> throwE "aselect: expected a literal key"

  -- Gather evidence required to perform the array operation.
  Refl <- failWithE "aselect: key type mismatch" $ eqLiteralType (literalType @k) kty

  -- Select the value out of the array and wrap it back into an expression.
  let val = Literal (literalType @v) $ Array.select arr key
  pure $ mkLit val

-- :: forall k v. Primitive k => Primitive v => Array k v -> k -> v -> Array k v
type ArrayStoreOp
  =   Forall 0 TypeKind
  :.  Forall 1 TypeKind
  :.  ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)
  :-> TyVar 0 TypeKind
  :-> TyVar 1 TypeKind
  :-> ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)

astore :: PrimOp es
astore = embed2 @ArrayStoreOp \_ _ arrE keyE valE -> do
  -- Get the inner array.
  SomeArray @k @v arr <- hoistEff arrE

  -- Gather the literal, knowing it is one due to the constraint.
  Literal kty key <- hoistEff keyE >>= \case
    Lit lit -> pure lit
    _ -> throwE "astore: expected a literal key"

  -- Gather the literal, knowing it is one due to the constraint.
  Literal vty val <- hoistEff valE >>= \case
    Lit lit -> pure lit
    _ -> throwE "astore: expected a literal value"

  -- Gather evidence required to perform the array operation.
  Refl <- failWithE "astore: key type mismatch" $ eqLiteralType (literalType @k) kty
  Refl <- failWithE "astore: value type mismatch" $ eqLiteralType (literalType @v) vty

  -- Create the modified array.
  let array = Array.store arr key val
  pure $ SomeArray array

type ArrayEqOp
  =   Forall 0 TypeKind
  :.  Forall 1 TypeKind
  :.  ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)
  :-> ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)
  :-> BoolTy

aeq :: PrimOp es
aeq = embed2 @ArrayEqOp \_ _ arrL arrR -> do
  SomeArray @kL @vL arrL' <- hoistEff arrL
  SomeArray @kR @vR arrR' <- hoistEff arrR

  Refl <- failWithE "Array equality: key type mismatch" $ eqLiteralType (literalType @kL) (literalType @kR)
  Refl <- failWithE "Array equality: value type mismatch" $ eqLiteralType (literalType @vL) (literalType @vR)
  pure $ arrL' .== arrR'
