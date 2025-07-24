{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MagicHash #-}

module Pantomime.Concrete
  ( Concrete (..)
  , concretise
  , concretise2
  ) where

import Prelude hiding ((<>))

import GHC.Plugins hiding (thNameToGhcName, integer, eqClass, boolTy)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Class (Class (..))
import GHC.Core.InstEnv (instanceDFunId)
import GHC.Tc.Utils.TcType (eqType)
import GHC.TypeLits (SomeNat(..), someNatVal)

import Grisette.Unified (EvalModeTag (..), DecideEvalMode)
import Grisette.Internal.SymPrim.Prim.Internal.Term (defaultValue)
import Grisette.SymPrim qualified as Grisette
import Grisette
  ( ToCon (..)
  , EvalSym (..)
  , Symbol
  , Term
  , SymBool (..)
  , SymIntN (..)
  , Mergeable
  , Model
  , ConRep (..)
  , evalSymToCon
  , indexed
  , pattern ConTerm
  , pattern SymTerm
  , pattern ForallTerm
  , pattern ExistsTerm
  , pattern NotTerm
  , pattern OrTerm
  , pattern AndTerm
  , pattern EqTerm
  , pattern DistinctTerm
  , pattern ITETerm
  , pattern AddNumTerm
  , pattern NegNumTerm
  , pattern MulNumTerm
  , pattern AbsNumTerm
  , pattern SignumNumTerm
  , pattern LtOrdTerm
  , pattern LeOrdTerm
  , pattern AndBitsTerm
  , pattern OrBitsTerm
  , pattern XorBitsTerm
  , pattern ComplementBitsTerm
  , pattern ShiftLeftTerm
  , pattern ShiftRightTerm
  , pattern RotateLeftTerm
  , pattern RotateRightTerm
  , pattern BitCastTerm
  , pattern BitCastOrTerm
  , pattern BVConcatTerm
  , pattern BVSelectTerm
  , pattern BVExtendTerm
  , pattern ApplyTerm
  , pattern DivIntegralTerm
  , pattern ModIntegralTerm
  , pattern QuotIntegralTerm
  , pattern RemIntegralTerm
  , pattern FPTraitTerm
  , pattern FdivTerm
  , pattern RecipTerm
  , pattern FloatingUnaryTerm
  , pattern PowerTerm
  , pattern FPUnaryTerm
  , pattern FPBinaryTerm
  , pattern FPRoundingUnaryTerm
  , pattern FPRoundingBinaryTerm
  , pattern FPFMATerm
  , pattern FromIntegralTerm
  , pattern FromFPOrTerm
  , pattern ToFPTerm
  )

import Language.Haskell.TH qualified as TH

import Control.Monad (forM, (>=>))

import Data.Constraint (Dict(..))
import Data.Data (TypeRep, type (:~:) (..), eqT)
import Data.Typeable (Typeable, cast)
import Data.Kind (Constraint)

import Pantomime.WordSize
import Pantomime.Value
import Pantomime.Runtime
import Pantomime.Util
import Pantomime.MonadEval hiding (UnsupportedExpr)
import Pantomime.Grisette.BitVector
import Pantomime.Grisette.Union
import Pantomime.Concrete.GrisetteOps
import Pantomime.Dict (normNumLitTy)
import Pantomime.DictMap (DictMap)
import Pantomime.DictMap qualified as DictMap

import Effectful
import Effectful.Error.Static
import Effectful.Grisette.Fresh
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.GHC.External
import Effectful.Dispatch.Static (unsafeEff_)
import Effectful.Exception (throwIO, ErrorCall (..))
import Effectful.Context

-- TODO: I think this is not the cleanest representation. We should make this
-- a bit better.
data Concrete where
  Record :: DataCon -> [Concrete] -> Concrete
  Function :: Symbol -> Type -> Concrete -> Concrete
  Value :: Show a => a -> Concrete
  Error :: RuntimeError -> Concrete
  Unknown :: Concrete

-- TODO: This isn't the nicest outputable instance. I think we want a concrete
-- to have a name, such that we can use pprConcrete to output the actual name
-- instead of a bunch of question marks. I additionally would like to emit the
-- type of each argument (and the final output). Ideally in Haskell style:
-- x :: Type
-- x = value
-- TODO: I guess we aren't really going to do this, since we won't be using this
-- format soon. What we should do though, it create a pretty printer which works
-- well for the kind of output produced by this conversion here.
--
-- Some things that we (might) want to implement:
-- - Record printing. I think this is incredibly important for clarity and I'm
--   not sure if GHC has a native print for this.
--
-- - Remove type and dictionary arguments for the primitive Grisette operations.
--   Ideally, the operators are also printed infix. My goal is to have it match
--   with how GHC would print other well-known typeclasses such as Num. It
--   should match the non-debug version btw, as that is the prettiest! The debug
--   info is unimportant for the use-case of Pantomime, and thus actually
--   hinders clarity.
--
-- - The printing in the sort of Haskell style with the type signature above is
--   also nice. Maybe we want some support for that!
--   x :: Type
--   x = value
instance Outputable Concrete where
  ppr = pprConcrete ("? =" <+>) id

pprConcrete
  :: (SDoc -> SDoc)
  -> (SDoc -> SDoc)
  -> Concrete
  -> SDoc
pprConcrete addHeader addParens = \case
  Record dataCon fields
    -- Is saturated tuple?
    | Just sort <- tyConTuple_maybe $ dataConTyCon dataCon
    , length fields == dataConSourceArity dataCon -> do
      let fields' = fsep $ punctuate comma (pprConcrete id id <$> fields)
      addHeader $ tupleParens sort fields'

    -- Is record?
    | labels <- dataConFieldLabels dataCon
    , length labels == dataConSourceArity dataCon -> do
      let header = addHeader $ ppr dataCon

      let prepend pre (name, value) = do
            pprConcrete (pre <+> ppr name <+> equals <+>) id value

      let fields' = vcat $ case zip labels fields of
            -- Add braces on the first and last line. The remaining ones start with
            -- a comma.
            x:xs -> prepend lbrace x : fmap (prepend comma) xs ++ [rbrace]
            -- Skip braces if we don't have fields
            [] -> []

      hang header 2 fields'

    | otherwise -> do
      let header = addHeader $ ppr dataCon
      let fields' = sep $ pprConcrete id parens <$> fields
      addParens $ hang header 2 fields'

  expr@(Function _ _ _) -> do
    let pprFun name ty = parens $ text (show name) <+> "::" <+> ppr ty

    let collectFuns (Function name ty inner) = do
          let (bndrs, body) = collectFuns inner
          ((name, ty):bndrs, body)
        collectFuns body = ([], body)

    let (bndrs, body) = collectFuns expr

    let args = sep $ uncurry pprFun <$> bndrs
    let header = addHeader $ "\\" <+> args <+> arrow

    let body' = pprConcrete id id body
    addParens $ hang header 2 body'

  Value value -> addHeader $ text (show value)
  Error err -> addHeader $ "RUNTIME ERROR" <+> ppr err
  Unknown -> addHeader $ "undefined"


dbg :: forall o es. Outputable o => o -> Eff es ()
dbg = unsafeEff_ . putStrLn . showSDocUnsafe . ppr

dbgS :: forall s es. Show s => s -> Eff es ()
dbgS = unsafeEff_ . print

-- TODO: I should be able to reconstruct a full CoreExpr from a Value. That
-- would be the ideal concrete form!
concretise
  :: forall es ws
   . Error EvalError :> es
  => Fresh :> es
  => KnownWordSize ws
  => Model
  -> Value (Eff es) ws
  -> Eff es Concrete
concretise model = \case
  Primitive prim -> do
    pure $ concretePrimitive model prim
  -- TODO: Clean this horrible piece of code up!
  Data adt -> do
    let tag = evalSymToCon @_ @(Tag C ws) model $ adtTag adt

    -- dbg' . show $ adtTag adt
    case unRuntimeC tag of
      Right tag'
        | Just dataCon <- tagToDataCon tag' $ adtTyCon adt
        , Just fields <- adtDataConFields adt dataCon -> do
          fields' <- forM fields $ concretise model
          pure $ Record dataCon fields'
        
      -- TODO: This shouldn't happen!
      Right _ -> pure Unknown
      Left Invalid -> pure Unknown
      Left err -> pure $ Error err

  -- TODO: Clean this horrible piece of code up!
  Cast' co value' -> go value' $ coercionRKind co
    where
      go value ty | not $ ty `eqType` coercionLKind co = do
        (tyCon, tys) <- whyFail IllTyped $ splitTyConApp_maybe ty
        dataCon <- whyFail IllTyped $ tyConSingleDataCon_maybe tyCon
        argTy <- case dataConInstArgTys dataCon tys of
          [argTy] -> pure $ scaledThing argTy
          _ -> throwError_ IllTyped
        arg' <- go value argTy
        pure $ Record dataCon [arg']
      go value _ = concretise model value

  Fun argTy _ -> do
    ident <- getIdentifier
    FreshIndex idx <- nextFreshIndex
    let symbol = indexed ident idx
    -- arg <- undefined
    -- res <- fun arg

    -- body <- concretise model res
    let body = Unknown
    pure $ Function symbol argTy body

  Poly _ty _ident -> pure $ Unknown

  -- TODO: This is super ugly!
  Opaque' ty value
    -- TODO Actually check the TyCon!
    | Just (_tyCon, [size]) <- tcSplitTyConApp_maybe ty
    , Just (SomeNat @n _) <- normNumLitTy size >>= someNatVal
    , Just bv <- cast @_ @(RuntimeValue S (WordN S n)) value
    -> pure $ primCon model bv

  Opaque' ty value
    -- TODO Actually check the TyCon!
    | Just (_tyCon, [size]) <- tcSplitTyConApp_maybe ty
    , Just (SomeNat @n _) <- normNumLitTy size >>= someNatVal
    , Just bv <- cast @_ @(RuntimeValue S (IntN S n)) value
    -> pure $ primCon model bv

  Opaque' ty value
    -- TODO Actually check the TyCon!
    | Just (_tyCon, []) <- tcSplitTyConApp_maybe ty
    , Just bv <- cast @_ @(RuntimeValue S (WordN S 1)) value
    -> pure $ primCon model bv

  Opaque' _ty _value -> pure $ Unknown

  -- TODO: There should be a better error to emit than this no? Maybe we
  -- should make a new one... Maybe we should make an error for concrete lookup
  -- failures. Alternatively, I guess we could actually just return the type as
  -- is no? It is actually also a concrete version in a sense.
  Ty _ -> throwError_ IllTyped
  Co _ -> throwError_ IllTyped

concretePrimitive
  :: forall ws
   . KnownWordSize ws
  => Model
  -> Primitive S ws
  -> Concrete
concretePrimitive model = \case
  Int value -> prim' value
  Int8 value -> prim' value
  Int16 value -> prim' value
  Int32 value -> prim' value
  Int64 value -> prim' value
  Word value -> prim' value
  Word8 value -> prim' value
  Word16 value -> prim' value
  Word32 value -> prim' value
  Word64 value -> prim' value
  Float value -> prim' value
  Double value -> prim' value
  ByteArray _ value -> prim' value
  where
    prim'
      :: forall a
       . ToCon a (ConType a)
      => EvalSym a
      => Show (ConType a)
      => RuntimeValue S a
      -> Concrete
    prim' = primCon model

-- TODO: Maybe give this a better name? This function is also kind of ugly...
primCon
  :: forall a
   . ToCon a (ConType a)
  => EvalSym a
  => Show (ConType a)
  => Model
  -> RuntimeValue S a
  -> Concrete
primCon model value = do
  let concrete = evalSymToCon @_ @(RuntimeValue C (ConType a)) model value
  case unRuntimeC concrete of
    Right value' -> Value $ value'
    Left err -> Error err

-- FIXME: The effect inside of 'Value' cannot match the ones in the method of
-- 'Concretise'. We cannot really resolve this until we remove the effects from
-- value completely.
concretise2
  :: forall es ws
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasInstEnvs :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => KnownWordSize ws
  => Model
  -> Value (Eff es) ws
  -> Eff es CoreExpr
concretise2 = go
  where
    go
      :: Model
      -> Value (Eff es) ws
      -> Eff es CoreExpr
    go model = \case
      Primitive (Int value) -> do
        dbgS @String $ "reached?"
        dbgS value
        case reverse . overestimateUnionValues $ unRuntimeS value of
          (Right (IntPW (IntP (SymIntN value')))):_ -> do
            Refl <- maybe undefined pure $ eqT @(WordBits ws) @64
            e <- runner $ concretise3 value'
            dbgS value
            dbg e
          _ -> pure ()
        undefined
      Primitive _ -> undefined
      -- TODO: This conversion from an ADT is actually quite a bit harder than
      -- what I had in mind initially. The problem being: how do we concretise
      -- the tag. If the tag is concrete, we would expect to get 
      Data _adt -> do
        undefined
      Poly _ _ -> undefined
      Fun _ _ -> undefined
      Cast' co value -> do
        expr <- go model value
        pure $ mkCast expr co
      Ty ty -> pure $ Type ty
      Co co -> pure $ Coercion co
      Opaque' _ _ -> undefined

    runner
      = (runErrorWith \cs (LookupError @(Class, [Type]) (cls, ty)) -> do
        dbgS cs
        dbg cls
        dbg ty
        error "cls ty lookup")
      . (runErrorWith \_ (LookupError @TypeRep _) -> do
        error "type rep lookup")
      . (runErrorWith \_ (LookupError @Id _) -> do
        error "id lookup")
      . runContextReader dicts

    dicts 
      = DictMap.insert @Grisette.IntN64
      . DictMap.insert @Bool
      $ DictMap.empty @CoreRep
  -- Primitive prim@(Int value) -> do
  --   dbgS @String $ "reached?"
  --   dbgS value
  --   case reverse . overestimateUnionValues $ unRuntimeS value of
  --     (Right (IntPW (IntP (SymIntN value')))):_ -> do
  --       Refl <- maybe undefined pure $ eqT @(WordBits ws) @64
  --       let dicts
  --             = DictMap.insert @Grisette.IntN64
  --             . DictMap.insert @Bool
  --             $ DictMap.empty
  --       let runner
  --             = (runErrorWith \cs (LookupError @(Class, [Type]) (cls, ty)) -> do
  --               dbgS cs
  --               dbg cls
  --               dbg ty
  --               error "cls ty lookup")
  --             . (runErrorWith \_ (LookupError @TypeRep _) -> do
  --               error "type rep lookup")
  --             . (runErrorWith \_ (LookupError @Id _) -> do
  --               error "id lookup")
  --       e <- runner $ termToCoreExpr dicts value'
  --       dbgS value
  --       dbg e
  --     _ -> pure ()
  --   pure $ concretePrimitive model prim

-- symbolToCoreExpr
--   :: TypedAnySymbol a
--   -> Eff es Id
-- symbolToCoreExpr = undefined
  -- unsafeEff_ . print $ symbol
  -- pure $ 
  -- undefined

class Concretise a where
  -- NOTE: Once GHC makes type family unfolding fast, we should give this the
  -- following definition. This should also happen for other typeclasses that
  -- use the same trick:
  --
  -- type ConcretiseE a :: [Effect]
  --
  -- Which should be usable via:
  --
  -- concretise :: ConcretiseE a :>> es => a -> Eff es CoreExpr
  type ConcretiseE a (es :: [Effect]) :: Constraint

  concretise3
    :: ConcretiseE a es
    => a
    -> Eff es CoreExpr

instance (DecideEvalMode mode, Mergeable a, Concretise a) => Concretise (Union mode a) where
  -- TODO: I guess the concretise function doesn't need the requirements for
  -- SymBool concretisation if 'C ~ mode'.
  type ConcretiseE (Union mode a) es =
    ( ConcretiseE a es
    , Error (LookupError TypeRep) :> es
    , Error (LookupError Id) :> es
    , Error (LookupError (Class, [Type])) :> es
    , Error (LookupError TH.Name) :> es
    , Error (LookupError Name) :> es
    , HasInstEnvs :> es
    , HasThings :> es
    , THNameToGHCName :> es
    , Context Reader (DictMap CoreRep) :> es
    )

  -- TODO: What if this is mutually recursive with whatever 'a' is? Then we
  -- still build up the callstack... I'm not sure what the solution to that
  -- would be...
  --
  -- The behaviour we likely want is to use the old callstack we first used to
  -- enter this function when we recurse. This actually seems like really easy
  -- behaviour to implement at runtime, but I'm worried the cost will be quite
  -- high: every call needs to check whether it wasn't called recursively...
  -- Note that in this setting, I see different typeclass implementations as
  -- different function.
  --
  -- Perhaps, a better solution would be if Haskell allowed HasCallStack
  -- constraints on typeclass constraints. Then we can just get the HasCallStack
  -- from the callsite. I guess it might be very opaque and difficult to work
  -- with though...
  --
  -- Idk, it seems like a truly difficult problem really...
  concretise3 @es = go
    where
      go :: Union mode a -> Eff es CoreExpr
      go = \case
        Single value -> concretise3 value
        If (SymBool cond) tr fl -> concretiseITE cond tr fl

concretiseITE
  :: forall a es
   . HasCallStack
  => Error (LookupError TypeRep) :> es
  => Error (LookupError Id) :> es
  => Error (LookupError (Class, [Type])) :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasInstEnvs :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Context Reader (DictMap CoreRep) :> es
  => ConcretiseE a es
  => Concretise a
  => Term Bool
  -> a
  -> a
  -> Eff es CoreExpr
concretiseITE cond tr fl = do
  -- Construct the scrutinee.
  scrut <- concretise3 cond

  -- FIXME: How do I get a good case binder for this? Perhaps I should just
  -- carry an InScopeSet in this function? This binder technically is fine btw,
  -- it's just not very nice really.

  -- Create the case binder.
  boolTy <- coreType @Bool
  let bndr = mkWildValBinder ManyTy boolTy

  -- Build the alternatives for the case expression.
  -- WARNING: We explicitly assume the the 'DataCon' to be 'False#' and 'True#',
  -- declared in that order.
  let dataCons = tyConDataCons $ tyConAppTyCon boolTy
  let zipped = zip dataCons [fl, tr]
  alts <- forM zipped \(dataCon, rhs) -> do
    rhs' <- concretise3 rhs
    pure $ Alt (DataAlt dataCon) [] rhs'

  -- Fetch the type of the alternatives.
  let ty = coreAltsType alts

  -- Gather all parts for the final case expression.
  pure $ Case scrut bndr ty alts

instance CoreRep a => Concretise (Term a) where
  -- TODO: I'm not sure I want all these errors. Especially the ones for Id and
  -- (Class, [Type]) seem sort of unclear? One way to make it slightly better is
  -- perhaps to have LookupError include the type of what we were looking up.
  -- Maybe only via an existential btw.
  type ConcretiseE (Term a) es =
    ( Error (LookupError TypeRep) :> es
    , Error (LookupError Id) :> es
    , Error (LookupError (Class, [Type])) :> es
    , Error (LookupError TH.Name) :> es
    , Error (LookupError Name) :> es
    , HasInstEnvs :> es
    , HasThings :> es
    , THNameToGHCName :> es
    , Context Reader (DictMap CoreRep) :> es
    )

  -- NOTE: It is important that the (mutually) recursive parts of this function
  -- are closures: we do not want to grow the 'CallStack' on every recursive
  -- unfolding. Instead, we now capture the 'CallStack' once upon function
  -- entry.
  concretise3 @es = go
    where
      -- | Main body of Term to Core Expression conversion.
      go
        :: forall b
         . CoreRep b
        => Term b
        -> Eff es CoreExpr
      go = \case
        ConTerm value -> coreInst value
        -- FIXME: This just constructs some bogus value instead of the symbol.
        -- It is not an easy thing to fix though. We need to create a symbol
        -- that can be converted back into a Var when constructing the Term.
        --
        -- TODO: One thing to keep in mind is that a symbol might actually also
        -- come from a tag. If we have e.g. 'x.tag' as a symbol, we want to
        -- convert it to 'dataToTag# x'. This is really important for a good
        -- conversion!
        SymTerm _symbol -> coreInst @b defaultValue
          -- Var <$> symbolToCoreExpr symbol
        -- FIXME: This call to 'concretiseITE' will recursively grow the
        -- callstack.
        ITETerm cond tr fl -> concretiseITE cond tr fl
        NotTerm value -> concreteApp 'not# [value]
        AndTerm lhs rhs -> concreteApp '(&&#) [lhs, rhs]
        OrTerm lhs rhs -> concreteApp '(||#) [lhs, rhs]
        EqTerm @_ @c lhs rhs -> do
          dicts <- get @(DictMap CoreRep)
          Dict <- DictMap.lookup @c dicts
          methodApp '(==#) [lhs, rhs]
        -- TODO: Implement 'Distinct'. I don't think it is generated much, if at
        -- all. I expect that most instances are just inequality of two values,
        -- so perhaps we can just generate pairwise comparisons?
        DistinctTerm _ -> undefined
        AddNumTerm lhs rhs -> methodApp '(+#) [lhs, rhs]
        NegNumTerm value -> methodApp 'negate# [value]
        MulNumTerm lhs rhs -> methodApp '(*#) [lhs, rhs]
        AbsNumTerm value -> methodApp 'abs# [value]
        SignumNumTerm value -> methodApp 'signum# [value]
        LtOrdTerm @_ @c lhs rhs -> do
          dicts <- get @(DictMap CoreRep)
          Dict <- DictMap.lookup @c dicts
          methodApp '(<#) [lhs, rhs]
        LeOrdTerm @_ @c lhs rhs -> do
          dicts <- get @(DictMap CoreRep)
          Dict <- DictMap.lookup @c dicts
          methodApp '(<=#) [lhs, rhs]
        AndBitsTerm lhs rhs -> methodApp '(.&.#) [lhs, rhs]
        OrBitsTerm lhs rhs -> methodApp '(.|.#) [lhs, rhs]
        XorBitsTerm lhs rhs -> methodApp '(.^.#) [lhs, rhs]
        ComplementBitsTerm value -> methodApp 'complement# [value]
        ShiftLeftTerm value idx -> methodApp 'shiftL# [value, idx]
        ShiftRightTerm value idx -> methodApp 'shiftR# [value, idx]
        RotateLeftTerm value idx -> methodApp 'rotateL# [value, idx]
        RotateRightTerm value idx -> methodApp 'rotateR# [value, idx]
        BitCastTerm _ -> undefined
        BitCastOrTerm _ _ -> undefined
        BVConcatTerm _ _ -> undefined
        BVSelectTerm _ _ _ -> undefined
        BVExtendTerm _ _ _ -> undefined
        ApplyTerm _ _ -> undefined
        DivIntegralTerm _ _ -> undefined
        ModIntegralTerm _ _ -> undefined
        QuotIntegralTerm _ _ -> undefined
        RemIntegralTerm _ _ -> undefined
        FPTraitTerm _ _ -> undefined
        FdivTerm _ _ -> undefined
        RecipTerm _ -> undefined
        FloatingUnaryTerm _ _ -> undefined
        PowerTerm _ _ -> undefined
        FPUnaryTerm _ _ -> undefined
        FPBinaryTerm _ _ _ -> undefined
        FPRoundingUnaryTerm _ _ _ -> undefined
        FPRoundingBinaryTerm _ _ _ _ -> undefined
        FPFMATerm _ _ _ _ -> undefined
        FromIntegralTerm _ -> undefined
        FromFPOrTerm _ _ _ -> undefined
        ToFPTerm _ _ _ _ -> undefined
        ForallTerm _ _ -> undefined
        ExistsTerm _ _ -> undefined

      -- | Typeclass method application.
      --
      -- We look up the template haskell name as an 'Id' that belongs to a
      -- method. We will fetch the instance of the 'CoreRep' of this term to
      -- resolve the dictionary constraint. Afterwards, we apply the arguments
      -- to the term.
      --
      -- NOTE:
      --
      -- This only supports methods of the form:
      -- > class Typeclass (a :: TYPE r) where
      -- >   method :: forall a. *(a ->) (a|concrete)
      --
      -- The number of provided arguments are not checked to match the arity of
      -- the method.
      methodApp
        :: forall b
         . CoreRep b
        => TH.Name
        -> [Term b]
        -> Eff es CoreExpr
      methodApp name args = do
        -- Get the core type and runtime representation of this term.
        ty <- coreType @b
        rep <- coreRuntimeRep @b

        -- Lookup the typeclass method Id and the corresponding typeclass.
        var <- lookupIdTH name
        cls <- case idDetails var of
          ClassOpId cls _ -> pure cls
          _ -> throwError_ $ LookupError var

        -- Lookup the class instance that corresponds to the primitive type.
        dict <- lookupUniqueDict cls [rep, ty]

        -- Construct the method and the arguments.
        let fun = mkApps (Var var) [Type ty, dict]
        args' <- forM args go

        -- Apply the method to the arguments.
        pure $ mkApps fun args'

      -- | Concrete function application.
      -- 
      -- This function will look up the template haskell name as an 'Id' and
      -- apply it directly to the arguments after converting them to 'CoreExpr'.
      --
      -- NOTE:
      -- 
      -- This only supports functions of the form:
      -- > function :: forall a. (a ->)* closed
      --
      -- The number of provided arguments are not checked to match the arity of
      -- the method.
      concreteApp
        :: forall b
         . CoreRep b
        => TH.Name
        -> [Term b]
        -> Eff es CoreExpr
      concreteApp name args = do
        -- Lookup the concrete function Id.
        var <- lookupIdTH name

        -- Construct the method and the arguments.
        let fun = Var var
        args' <- forM args go

        -- Apply the method to the arguments.
        pure $ mkApps fun args'

-- | Representation of Grisette types when converted to GHC Core.
--
-- The instance should satisfy the following:
--
-- [Concrete Type]
-- The type consists only of concrete type constructors, concrete type variables
-- and applications.
--
-- [RuntimeRep Kind]
-- The kind of the 'coreType' should be 'TYPE r'.
--
-- [Instance Conversion]
-- The resulting expression from converting a literal using 'coreInst' should
-- match the type of 'coreType'.
class Typeable a => CoreRep a where
  -- | The GHC Core 'Type' of this Grisette type.
  coreType
    :: HasCallStack
    => Error (LookupError TH.Name) :> es
    => Error (LookupError Name) :> es
    => THNameToGHCName :> es
    => HasThings :> es
    => Eff es Type
  -- | Conversion function from a concrete Grisette instance to GHC Core.
  coreInst
    :: HasCallStack
    => Error (LookupError TH.Name) :> es
    => Error (LookupError Name) :> es
    => THNameToGHCName :> es
    => HasThings :> es
    => a
    -> Eff es CoreExpr

-- | Fetch the runtime representation of a Grisette primitive.
coreRuntimeRep
  :: forall a es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => CoreRep a
  => Eff es RuntimeRepType
coreRuntimeRep = do
  ty <- coreType @a
  let kind = typeKind ty
  case sORTKind_maybe kind of
    Just (TypeLike, rep) -> pure rep
    _ -> throwIO $ ErrorCall "INTERFACE MISUSE: kind of 'coreType' was not 'TYPE r'"

instance CoreRep Bool where
  coreType = mkTyConTy <$> lookupTyConTH ''Bool#
  coreInst = fmap (Var . dataConWorkId) . \case
    False -> lookupDataConTH 'False#
    True -> lookupDataConTH 'True#

instance CoreRep (Grisette.IntN 8) where
  coreType = mkTyConTy <$> lookupTyConTH ''Int8#
  coreInst = pure . Lit . LitNumber LitNumInt8 . toInteger 

instance CoreRep (Grisette.IntN 16) where
  coreType = mkTyConTy <$> lookupTyConTH ''Int16#
  coreInst = pure . Lit . LitNumber LitNumInt16 . toInteger 

instance CoreRep (Grisette.IntN 32) where
  coreType = mkTyConTy <$> lookupTyConTH ''Int32#
  coreInst = pure . Lit . LitNumber LitNumInt32 . toInteger 

instance CoreRep (Grisette.IntN 64) where
  coreType = mkTyConTy <$> lookupTyConTH ''Int64#
  coreInst = pure . Lit . LitNumber LitNumInt64 . toInteger 

-- | Lookup an 'Id' given a template haskell 'Name'.
lookupIdTH
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => TH.Name
  -> Eff es Id
lookupIdTH = thNameToGhcName >=> lookupId

-- | Lookup a 'TyCon' given a template haskell 'Name'.
lookupTyConTH
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => TH.Name
  -> Eff es TyCon
lookupTyConTH = thNameToGhcName >=> lookupTyCon

-- | Lookup a 'DataCon' given a template haskell 'Name'.
lookupDataConTH
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => TH.Name
  -> Eff es DataCon
lookupDataConTH = thNameToGhcName >=> lookupDataCon

-- | Lookup a dictionary for a class instance.
--
-- This will only return if the instance was unique.
lookupUniqueDict
  :: HasCallStack
  => Error (LookupError (Class, [Type])) :> es
  => HasInstEnvs :> es
  => Class
  -> [Type]
  -> Eff es CoreExpr
lookupUniqueDict cls tys = do
  (inst, args) <- lookupUniqueInst cls tys
  let inst' = Var $ instanceDFunId inst
  let args' = fmap Type args
  pure $ mkApps inst' args'

-- runtimeToExpr
--   :: RuntimeValue C a
--   -> (a -> CoreExpr)
--   -> CoreExpr
-- runtimeToExpr value convert = do
--   let primOpId = Var . primOpWrapperId
--   case unRuntimeC value of
--     Right value' -> convert value'
--     Left Overflow -> primOpId RaiseOverflowOp `App` unboxedUnitExpr
--     Left Underflow -> primOpId RaiseUnderflowOp `App` unboxedUnitExpr
--     Left DivideByZero -> primOpId RaiseDivZeroOp `App` unboxedUnitExpr
--     Left Invalid -> mkApps (primOpId RaiseOp)
--       [ Type liftedRepTy
--       , Type unitTy
--       , unitExpr
--       ]
