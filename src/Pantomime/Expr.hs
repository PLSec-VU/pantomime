{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}

module Pantomime.Expr
  ( Eval
  , Runtime
  , RuntimeT (..)
  , pattern Runtime
  , runRuntime
  , pattern RuntimeT
  , runRuntimeT
  , Variant (..)
  , Expr (..)
  , Spine
  , Arg
  , Literal (..)
  , Type
  , Coercion
  , Constructor (..)

  , pprExpr
  , pprArg
  , pprRuntime

  , mkDataCon
  , mkEnumCon
  , mkBitVec
  , mkInteger
  , mkBool
  , mkCon
  , mkLit
  , mkArray
  , mkType
  , mkCoercion
  , mkLam
  , mkApp
  , mkApps
  , mkCastMCo
  , mkCast

  , mkUnreachable
  , mkUB
  , mkRaise

  , forceTyCo
  , forceTy
  , forceCo

  , eqType
  , eqCon
  , exprType
  , collectArgs
  , collectScrut

  , liftEff
  , hoistEff
  , thunk
  , deferE
  , throwE
  , failWithE
  , dbgE
  ) where

import GHC.Plugins qualified as GHC
import GHC.Core.Type qualified as GHC
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Ppr (pprOptCo)
import GHC.Core.Predicate (isEqPred)
import GHC.Core.Opt.Arity (pushCoTyArg, pushCoValArg)
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  , SDoc
  , ($+$)
  , parens
  , hang
  , nest
  )
import GHC.Plugins
  ( Type
  , Coercion
  , CoercionR
  , MCoercionR
  , MCoercion (..)
  , Role (..)
  , TyCon
  , DataCon
  , isEnumerationTyCon
  , dataConTagZ
  , dataConTyCon
  , isFunTy
  , isForAllTy
  , coercionRole
  , coercionLKind
  , isReflexiveCo
  , mkTransCo
  , coercionRKind
  , mkCoCast
  , isForAllTy_ty
  , coercionType
  , splitFunTy_maybe
  , splitForAllTyCoVar_maybe
  , tyConDataCons
  , mkCoercionTy
  , tyCoVarsOfTypes
  , mkInScopeSet
  , splitTyConApp_maybe
  , dataConExTyCoVars
  , dataConWorkId
  , dataConRepArgTys
  , splitAtList
  , dropList
  , dataConUnivTyVars
  , decomposeCo
  , tyConArity
  , tyConRolesRepresentational
  , liftCoSubstWithEx
  , varType
  )

import GHC.Generics (Generic)
import GHC.Stack (withFrozenCallStack)

import Grisette
  ( Union
  , SymBool
  , SymInteger
  , SymEq (..)
  , ToSym (..)
  , ToCon (..)
  , TryMerge (..)
  , Mergeable (..)
  , Mergeable1 (..)
  , SimpleMergeable (..)
  , SimpleMergeable1 (..)
  , SymBranching (..)
  , MergingStrategy (..)
  , EvalSym (..)
  , EvalSym1 (..)
  , Default (..)
  , wrapStrategy
  , liftUnion
  , pattern Single
  , pattern If
  )
-- TODO: Change import once we fully integrate SymArray into grisette! Right
-- now, we still need to touch these internal things...
import Grisette.Internal.SymPrim.SymArray (SymArray)

import Pantomime.Literal
import Pantomime.Orphan.Effectful ()
import Pantomime.Orphan.GHC ()
import Pantomime.Grisette.UnionT
import Pantomime.Grisette.Mergeable (impossible)
import Pantomime.Util
  ( SomeBitVec (..)
  , SymBitVec
  , BitVec
  , KnownPos
  , failWith
  , dbg
  )

import Data.Composition ((.:))
import Data.Coerce (coerce)
import Data.List ((!?))
import Data.Traversable (for)
import Data.Typeable (type (:~:) (..), eqT)

import Control.Arrow (Arrow (..), (>>>))
import Control.Monad ((>=>), foldM, unless)
import Control.Monad.Except (ExceptT (..))
import Control.Monad.Identity (Identity (..))
import Control.Monad.Trans (MonadTrans (..))

import Effectful
import Effectful.Context
import Effectful.Error.Static
import Pantomime.Defer (defer, Deferrable, Defer (..))
import GHC.IO (unsafeDupablePerformIO)
import Effectful.Dispatch.Static (unEff)

-- TODO: I recently swapped this implementation from another one because I
-- thought the old one was broken w.r.t. laziness. I found out later that the
-- test case was just wrong (i.e. really infite, this one would also not pass
-- it). I'd like to see if we can reintroduce the old one, as I liked not having
-- the Result within the Union. In fact, I think this style of Result would
-- actually allow general effects to be available inside of Eval. The caveat
-- here is that the branches do not actually branch for the effects themselve.
-- This doesn't seem like a bad restriction though. For most effects: i.e.
-- errors and reader this is no real problem: we only care about the first error
-- anyways and reading does not require ordering anyway. For something like
-- state or writer, it could be a little bit more iffy. I guess we should
-- document this if we do want to allow full effects!
--
-- Just so I can find it later, this was the commit hash with the diff:
-- 29b937f6a911dace85647615c18d278bdbc6b0a7
--
-- I actually tried the old one, indeed it was **not** broken. Now I'm not
-- entirely sure which one I should favor... This one has the nice property of
-- not requiring a 'for' and 'join' on the inner union for the monadic bind.
-- I'm not sure if this one would work if we want to do a full Eff system in
-- place of just Result though. On the other hand though, I'm not sure if it was
-- slow to do a 'for' and then 'join' (and if there maybe is a better way).
--
-- Actually, I was thinking about how to write a 'UnionT' monad transformer
-- to wrap the around the Eff monad. Interestingly, the 'for' and 'join'
-- implementation is exactly like a broken 'ListT'. Note, the way it is broken
-- is very different from the reason I thought it was broken. It actually has
-- to do with commutativity of the monadic bind.
--
-- We can think if it is possible to write a non-broken UnionT, but for now it
-- is fine to leave it implemented like this I guess. Probably good to look at
-- the non-broken ListT implementations in order to find out how to write a good
-- one for Union. Perhaps the merging makes it a little bit hard...
--
-- For now though, let's just not bother and use this one!
--
-- Btw, I guess Either is commutative up to which error it emits. For us, any
-- arbitrary decision on this is fine. Reader is also commutative. I guess for
-- those two, we could actually implement Eval using the 'for' and 'join'
-- method, with the asterix of picking an arbitrary error branch. Having a
-- reader could be quite nice btw. We should employ the same trick as for the
-- error when indexing it btw!
--
-- I don't believe it is actually possible to write a good UnionT
-- implementation. That is, what would the effect be of two computations that
-- should be merged. Should we take just one of them? Which one? If we do take
-- effects of both, which ordering should be employed for this?
--
-- Still, having to redefine an effect-like monad restricted to the correct
-- effects feels a tad bit silly. Would it not make more sense to just have a
-- big warning of which effects are actually allowed by this?
--
-- TODO: So I've changed Eval now to allow full commutative effects. The text
-- above should probably be compiled into some sort of reasoning why we chose
-- for this setup. There also should be a big warning sign of the commutativity
-- restriction, we can refer to UnionT for this as I explain much of how it
-- works there.
-- newtype Eval es a where
--   Eval :: ExceptT (Variant es) (UnionT (Eff es)) a -> Eval es a
--   deriving Functor
--   deriving Applicative
--   deriving Monad
--   deriving TryMerge
--   deriving Mergeable
--   deriving Mergeable1
--   deriving SimpleMergeable
--   deriving SimpleMergeable1
--   deriving SymBranching
--   deriving EvalSym
--   deriving EvalSym1
type Eval es = RuntimeT (Eff es)

type Runtime = RuntimeT Identity

newtype RuntimeT m a where
  RuntimeT' :: ExceptT Variant (UnionT m) a -> RuntimeT m a
  deriving Functor
  deriving Applicative
  deriving Monad
  deriving TryMerge
  deriving Mergeable
  deriving Mergeable1
  deriving SimpleMergeable
  deriving SimpleMergeable1
  deriving SymBranching
  deriving EvalSym
  deriving EvalSym1

instance MonadTrans RuntimeT where
  lift = RuntimeT' . lift . lift

instance Outputable (Runtime Expr) where
  ppr = pprRuntime pprExpr id

pattern Runtime :: Union (Either Variant a) -> Runtime a
pattern Runtime m <- (coerce -> m)
  where
    Runtime = coerce

runRuntime ::Runtime a -> Union (Either Variant a)
runRuntime = coerce

pattern RuntimeT :: m (Union (Either Variant a)) -> RuntimeT m a
pattern RuntimeT m <- (coerce -> m)
  where
    RuntimeT = coerce

runRuntimeT :: RuntimeT m a -> m (Union (Either Variant a))
runRuntimeT = coerce

-- TODO: I'm not sure if I like this name. Perhaps we can think about what other
-- options these have. Unlike the other error types, these ones don't need a
-- stack trace, as they're actually just valid values. In fact, I **really**
-- want these to merge! Perhaps something like NominalExcept/Error? Otherwise,
-- RuntimeAlt?
data Variant where
  UB :: Variant
  Unreachable :: Variant
  -- TODO: Should this not contain an Expr or EvalExpr? In any case, we haven't
  -- really implemented errors yet, so we should just look into this still.
  --
  -- Future reference, we have implemented raise# using the EvalExpr for now.
  -- I guess we'll have to see if this actually makes sense, but we don't do
  -- much with errors anyway still.
  Raise :: Spine -> Variant
  deriving Generic
  deriving Mergeable via Default Variant
  deriving EvalSym via Default Variant

-- TODO: I feel like a comment on this one is due: this is pretty much the main
-- data structure of the evaluator (together with Eval)!
data Expr where
  Lit
    :: Literal
    -> Expr
  Con
    :: Constructor
    -> Expr
  Type
    :: Type
    -> Expr
  Coercion
    :: Coercion
    -> Expr
  Lam
    :: Type
    -- ^ Expression type
    -> (Arg -> Spine)
    -- ^ Closure
    -> Expr
  -- TODO: I guess the only time App is used is for DataCon. Maybe having it
  -- in here is too general and it should just be part of DataCon? I guess
  -- technically a Cast might also be at the root no? Whilst we do fold casts
  -- over FunCo, we don't actually handle the case where a Cast occurs and it is
  -- not over a FunCo as root right now. I'll have to think about what's best.
  --
  -- I guess if the cast is not a FunCo or ForAllCo, at some point the execution
  -- will halt anyway once we want to pattern match on it though. Maybe indeed,
  -- only DataCon needs arguments. We do actually push over TyConAppCo. This is
  -- handle by pushCoArg.
  --
  -- VERDICT: I don't see a reason to keep the App node.
  App
    :: Expr
    -> Thunk
    -> Expr
  Cast
    :: Union Expr
    -> CoercionR
    -> Expr
  deriving Generic
  deriving Mergeable via Default Expr

instance EvalSym Expr where
  evalSym fill model = \case
    Lit lit -> Lit $ evalSym' lit
    Con con -> Con $ evalSym' con
    Type ty -> Type ty
    Coercion co -> Coercion co
    Lam ty closure -> Lam ty $ evalSym' . closure
    App fun arg -> App (evalSym' fun) (evalSym' arg)
    Cast body co -> Cast (evalSym' body) co
    where
      evalSym' :: EvalSym a => a -> a
      evalSym' = evalSym fill model

instance Outputable Expr where
  ppr = pprExpr id

-- | Expressions within the evaluation context. You may also think of these as
-- thunks. It is expected that the spine of this expression is never a 'Type' or
-- 'Coercion'.
type Spine = Runtime Expr

-- | Like 'EvalExpr', this may be considered a thunk. Unlike 'EvalExpr', this is
-- an expression that may appear in the argument position. This entails that
-- it may be a 'Type' or 'Coercion' in the spine.
type Arg = Runtime Expr

-- TODO: For now, I've made this Thunk so data constructors with different
-- existentials applications do not merge. I'm not sure whether perhaps it is
-- completely okay to let them merge btw, so we'd have to try this out. Perhaps
-- we can get rid of it.
--
-- Alternatively, we could write a custom merge strategy that will look at the
-- inner argument when it determines it should be a type or coercion.
--
-- Still, I'm somewhat convinced that we actually might just optimise error
-- branches (that occurred due to existentials) away. If this is true, I feel
-- like universal type arguments should perhaps just be part of the DataCon
-- literal. Then we can get rid of this thunk data type.
--
-- Note that one thing that happens with this is that at some time during eval
-- we might get a Union of expressions with different types. Not sure how to
-- feel about that...
--
-- After Tests:
---------------
-- We indeed reduce the bad branches away. I'm not sure about what would be the
-- best in terms of raw evaluation speed. This version requires an evaluation
-- of the right hand side of a case for every existential instance. This seems
-- somewhat unwanted.
--
-- The alternative is to have an (Eval TvSubstEnv) and (Eval CvSubstEnv) inside
-- of our Subst. Then at usage site we will have the errors in the leaves
-- instead. I feel like this is better, but idk. There is really only one way to
-- find out, which is to actually evaluate it.
--
-- Unwrapping the Eval Type outside of the TvSubstEnv is definitely not the
-- right move though. In this case, we may run many more branches than required
-- as we run a permutation of every possible pair of existential types (even
-- pairs that will not exist) for the entire rhs. In other words, we will
-- possibly run many more instances if we allow existential types to merge
-- without wrapping the substitition environment inside of Eval.
--
-- Having it inside means that we will run the
-- error branches where the existential is actually used.
--
-- NOTE on existentials:
-- If we are to fully put the universal and existential arguments in the
-- DataCon, then remember the following: the existential field only needs to be
-- of type [Type]. This feels counter-intuitive since the existential variables
-- field is of type TyCoVar. Still, this is correct. Coercions should simply be
-- wrapped via the use of mkCoercionTy. It took me a long time to figure this
-- out, so I wrote it down here!
data Thunk where
  Thunked :: Arg -> Thunk
  Forced :: Either Type Coercion -> Thunk
  deriving Generic
  deriving Mergeable via Default Thunk

instance EvalSym Thunk where
  evalSym fill model = \case
    Thunked value -> Thunked $ evalSym fill model value
    Forced value -> Forced value

data Constructor where
  DataCon
    :: DataCon
    -> Constructor
  EnumCon
    :: KnownPos n
    => SymBitVec n
    -> TyCon
    -> Constructor

instance Outputable Constructor where
  ppr = \case
    -- TODO: This should output the tag directly if concrete. If not and this is
    -- an enumeration TyCon, we should emit a tagToEnum# apply to the value. If
    -- this is not an enumeration TyCon, then the tag is invalid. We should
    -- probably print some sort of error message in that case.
    DataCon dc -> ppr dc
    EnumCon @n tag tc
      | Just tag' <- toCon @_ @(BitVec n) tag
      , Just dc <- tyConDataCons tc !? fromIntegral tag' -> ppr dc
      -- TODO: Technically this print is wrong as the type application should be
      -- the whole type, not just the TyCon.
      | otherwise -> "tagToEnum#" <+> "@" GHC.<> ppr tc <+> text (show tag)

instance Mergeable Constructor where
  rootStrategy = SortedStrategy
    (\case
      DataCon {} -> True
      EnumCon {} -> False)
    \case
      True -> wrapStrategy
        rootStrategy
        DataCon
        \case DataCon dc -> dc ; _ -> impossible

      False -> wrapStrategy
        rootStrategy
        (\(SomeBitVec tag, tc) -> EnumCon tag tc)
        \case EnumCon tag tc -> (SomeBitVec tag, tc) ; _ -> impossible

instance EvalSym Constructor where
  evalSym fill model = \case
    DataCon dc -> DataCon dc
    EnumCon tag tc -> EnumCon (evalSym fill model tag) tc

mkDataCon
  :: forall n
   . KnownPos n
  => DataCon
  -> Constructor
mkDataCon dc = if
  | let tc = dataConTyCon dc
  , isEnumerationTyCon tc -> do
    let tag = fromIntegral . dataConTagZ $ dc
    EnumCon @n tag tc
  | otherwise -> DataCon dc

-- TODO: Since we don't check bounds on creation anymore, this function seems
-- a bit more complex than it needs to be. That is, we can also just construct
-- it without the whole type.
mkEnumCon
  :: forall n es
   . KnownPos n
  => Deferrable es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => SymBitVec n
  -> Type
  -> Eval es Expr
mkEnumCon tag ty = do
  -- Ensure we have an enumeration type.
  (tc, targs) <- failWithE () $ splitTyConApp_maybe ty
  unless (isEnumerationTyCon tc) do
    throwE ()

  -- Construct the data constructor and its type arguments.
  let dc = mkCon $ EnumCon tag tc
  let targs' = pure . mkType <$> targs
  mkApps dc targs'

-- | Get the 'TyCon' of a constructor.
constructorTyCon :: Constructor -> TyCon
constructorTyCon = \case
  DataCon dc -> dataConTyCon dc
  EnumCon _tag tc -> tc

-- | Get the 'Type' of a constructor.
constructorType
  :: Error () :> es
  => Constructor
  -> Eff es Type
constructorType con = do
  dc <- case con of
    DataCon dc -> pure dc
    EnumCon _tag tc
      | dc : _ <- tyConDataCons tc -> pure dc
      | otherwise -> throwError ()
  pure $ varType (dataConWorkId dc)

pprExpr
  :: (SDoc -> SDoc)
  -> Expr
  -> SDoc
pprExpr addParens = \case
  Lit lit -> ppr lit
  Con con -> ppr con
  Type ty -> "@" GHC.<> ppr ty
  Coercion co -> "@~" GHC.<> ppr co
  Cast expr co -> do
    let expr' = pprUnion pprExpr parens expr
    addParens $ sep
      [ expr'
      , "`cast`" <+> pprOptCo co
      ]
  -- TODO: This one is a bit more difficult. Really the only way to print a
  -- lambda is to provide it with fresh arguments. The problem is that we need
  -- a lot more context for printing in that way.
  Lam {} -> "TODO lambda"
    -- (result, args) <- saturateLam @64 $ mkExpr expr
    -- let bndrs = fst <$> args
    -- let bndr = "\\" <+> sep (ppr <$> bndrs) <+> GHC.arrow
    -- body <- pprExpr id result
    -- pure . addParens $ hang bndr 2 body
  expr@App {} -> do
    let (fun, args) = collectArgs expr
    let header = pprExpr parens fun
    let args' = pprArg parens <$> args
    let body = sep args'
    addParens $ hang header 2 body

pprArg
  :: (SDoc -> SDoc)
  -> Arg
  -> SDoc
pprArg = pprRuntime pprExpr

pprRuntime
  :: forall a
   . Mergeable a
  => ((SDoc -> SDoc) -> a -> SDoc)
  -> (SDoc -> SDoc)
  -> Runtime a
  -> SDoc
pprRuntime inner = do
  coerce $ pprUnion \addParens -> \case
    Left alt -> case alt of
      UB -> "UB"
      Unreachable -> "Unreachable"
      Raise expr -> "raise#" <+> pprArg addParens expr
    Right value -> inner addParens value

pprUnion
  :: Mergeable a
  => ((SDoc -> SDoc) -> a -> SDoc)
  -> (SDoc -> SDoc)
  -> Union a
  -> SDoc
pprUnion inner addParens = \case
  Single value -> inner addParens value
  If scrut true false -> do
    -- Vertically concatenate using ($+$).
    let vcat' = foldl' @[] ($+$) GHC.empty

    -- Hang that always aligns vertically.
    let hang' d1 n d2 = vcat' [d1, nest n d2]

    -- Pretty print branches.
    let true' = pprUnion inner parens true
    let false' = pprUnion inner parens false

    -- Hange the branches below an if-then-else.
    addParens . hang' "ite" 2 $ vcat'
      [ text $ show scrut
      , true'
      , false'
      ]

-- TODO: I feel like these mkX for literals should create an Expr. Otherwise,
-- one would just use the literal constructor no? Especially since they're
-- patterns anyway, so any additional code required in their construction can
-- just be placed in there.
mkBitVec
  :: KnownPos n
  => SymBitVec n
  -> Literal
mkBitVec = BitVec

mkInteger
  :: SymInteger
  -> Literal
mkInteger = Integer

mkBool
  :: SymBool
  -> Literal
mkBool = Bool

mkArray
  :: LiteralTypeable k
  => LiteralTypeable v
  => SymArray k v
  -> Literal
mkArray = Array

mkCon
  :: Constructor
  -> Expr
mkCon = Con

mkLit
  :: Literal
  -> Expr
mkLit = Lit

mkType
  :: Type
  -> Expr
mkType = Type

mkCoercion
  :: Coercion
  -> Expr
mkCoercion = Coercion

mkLam
  :: Deferrable es
  => Type
  -> (Arg -> Eval es Expr)
  -> Eval es Expr
mkLam ty closure = Lam ty <$> deferE closure

mkApp
  :: HasCallStack
  => Deferrable es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr
  -> Arg
  -> Eval es Expr
mkApp fun arg = case fun of
  Cast body co -> do
    (arg', rco) <- liftEff $ pushCoArg co arg
    body' <- liftUnion body
    expr <- mkApp body' arg'
    mkCastMCo expr rco
  Lam _ty closure -> hoistEff $ closure arg
  _ -> liftEff do
    ty <- exprType fun
    if
      | isFunTy ty -> pure $ App fun (Thunked arg)
      | isForAllTy ty -> do
        forced <- forceTyCo arg
        pure $ App fun (Forced forced)
      | otherwise -> throwError ()

pushCoArg
  :: HasCallStack
  => Deferrable es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => CoercionR
  -> Arg
  -> Eff es (Arg, MCoercionR)
pushCoArg co arg = if
  | tyL <- coercionLKind co
  , isForAllTy_ty tyL -> do
    -- The argument needs to be a type. As such, we can force it.
    ty <- forceTy arg

    -- Attempt to push the coercion into the type argument.
    (ty', rco) <- failWith () $ pushCoTyArg co ty

    -- Return the type argument and result coercion.
    pure (pure $ mkType ty', rco)

  | otherwise -> do
    -- Attempt to split the coercion into an argument and result coercion.
    (aco, rco) <- failWith () $ pushCoValArg co

    -- Cast the argument and return the result coercion.
    arg' <- thunk do
      arg' <- hoistEff arg
      mkCastMCo arg' aco

    pure (arg', rco)

mkApps
  :: HasCallStack
  => Deferrable es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr
  -> [Arg]
  -> Eval es Expr
mkApps = foldM mkApp

mkCastMCo
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr
  -> MCoercionR
  -> Eval es Expr
mkCastMCo expr = \case
  MRefl -> pure expr
  MCo co -> mkCast expr co

mkCast
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr
  -> CoercionR
  -> Eval es Expr
mkCast expr co = do
  -- Ensure the coercion has role representational.
  unless (coercionRole co == Representational) do
    -- FIXME: Make this a proper error.
    throwE ()

  -- Ensure the cast can be applied to the expression.
  ty <- liftEff $ exprType expr
  unless (eqType ty $ coercionLKind co) do
    -- FIXME: Make this a proper error.
    throwE ()

  case expr of
    Cast body co' -> do
      let coT = mkTransCo co' co
      if
        | isReflexiveCo coT -> liftUnion body
        | otherwise -> pure $ Cast body coT

    -- NOTE: This comment was written originally inside of GHC 'mkCast'. I'm
    -- unsure what 'g' refers to (it's not in the original code either), but
    -- I'll keep the guard check here as it is probably important.
    --
    -- ```
    -- The guard here checks that g has a (~#) on both sides, otherwise
    -- 'decomposeCo' fails. Can in principle happen with unsafeCoerce.
    -- ```
    Coercion co' | isEqPred $ coercionRKind co -> do
      pure $ mkCoercion (mkCoCast co' co)

    -- TODO: Even with this improvement, we still do reflexivity check (and
    -- the above sanity type-check) once for each body. Perhaps we should take
    -- an 'Arg es' here?
    _
      | isReflexiveCo co -> pure expr
      | otherwise -> pure $ Cast (pure expr) co

mkVariant :: Variant -> Eval es a
mkVariant = RuntimeT . pure . pure . Left

mkUnreachable :: Eval es a
mkUnreachable = mkVariant Unreachable

mkUB :: Eval es a
mkUB = mkVariant UB

mkRaise :: Runtime Expr -> Eval es a
mkRaise = mkVariant . Raise

-- | Force an expression into a type or coercion.
--
-- A type or coercion is always terminating. Within a union they should
-- additionally always be a single. As such, we can escape the monad here.
--
-- WARNING: In general, expressions may be non-terminating. Use only when a Type
-- or Coercion is the expected result.
forceTyCo
  :: forall es
   . HasCallStack
  => Error () :> es
  => Arg
  -> Eff es (Either Type Coercion)
forceTyCo = runRuntime >>> \case
  -- Attempt to get a single 'Type' or 'Coercion'.
  Single (Right value)
    | Type ty <- value -> pure $ Left ty
    | Coercion co <- value -> pure $ Right co

  -- The expression was not in the expected shape.
  _ -> throwError ()

-- | Force an expression into a type using 'forceTyCo'.
forceTy
  :: HasCallStack
  => Error () :> es
  => Arg
  -> Eff es Type
forceTy = forceTyCo >=> either pure (const $ throwError ())

-- | Force an expression into a coercion using 'forceTyCo'.
forceCo
  :: HasCallStack
  => Error () :> es
  => Arg
  -> Eff es Coercion
forceCo = forceTyCo >=> either (const $ throwError ()) pure

-- | Equivalence between constructors.
--
-- Will throw an error if the types do not match.
eqCon
  :: HasCallStack
  => Error () :> es
  => Constructor
  -> Constructor
  -> Eff es SymBool
eqCon = \cases
  (DataCon ldc) (DataCon rdc)
    | dataConTyCon ldc == dataConTyCon rdc -> pure $ toSym (ldc == rdc)
  (EnumCon @l ltag ltc) (EnumCon @r rtag rtc)
    | ltc == rtc
    , Just Refl <- eqT @l @r -> pure $ ltag .== rtag
  _ _ -> throwError ()

-- TODO: This function deserves some clean-up! My syntax highlighter is even
-- breaking on it...
exprType
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr
  -> Eff es Type
exprType = \case
  Lit lit -> embedLitTyOf lit
  Con con -> constructorType con
  Type _ -> throwError ()
  Coercion co -> pure $ coercionType co
  Lam ty _ -> pure ty
  App fun arg -> do
    -- TODO: Recursive call grows callstack, fix this!
    fty <- exprType fun
    if
      | Just (var, rty) <- splitForAllTyCoVar_maybe fty -> do
        aty <- case arg of
          Forced (Right co) -> pure $ mkCoercionTy co
          Forced (Left ty) -> pure ty
          _ -> throwError ()
        let scope = mkInScopeSet $ tyCoVarsOfTypes [aty, rty]
        let subst = GHC.extendTCvSubst (GHC.mkEmptySubst scope) var aty
        pure $ GHC.substTy subst rty

      | Just (_, _, _, rty) <- splitFunTy_maybe fty -> pure rty

      | otherwise -> throwError ()
  Cast _ co -> pure $ coercionRKind co

-- | Collect the arguments of an application.
collectArgs
  :: Expr
  -> (Expr, [Arg])
collectArgs = second (fmap unthunk) . collectThunks

-- | Collect the thunks of an application.
collectThunks
  :: Expr
  -> (Expr, [Thunk])
collectThunks = go []
  where
    go args = \case
      App fun arg -> go (arg: args) fun
      expr -> (expr, args)

-- | Transform thunks into arguments.
--
-- Really, args are just always thunks. This will put forced values into thunks.
unthunk
  :: Thunk
  -> Arg
unthunk = \case
  Thunked value -> value
  Forced value -> case value of
    Right co -> pure $ mkCoercion co
    Left ty -> pure $ mkType ty

-- TODO: I wonder if it doesn't make more sense to just make this a
-- 'collectCon'? The part about collecting literals feels like it should not
-- live here, as it is specific to the bindings with Haskell. The Coercion part
-- feels also a bit misplaced.
--
-- Actually, we changed it now because as it turns out, you can also scrutinise
-- other stuff. For example, a function can be scrutinised. Not that you can
-- actually pattern match it, but it is valid to match 'DEFAULT' on it and just
-- use it to force the value!
-- | Collect the arguments of a scrutinee.
--
-- This will drop any universal type applications as these are not necessary for
-- pattern matching. Additionally, this will push a TyCon Coercion into the
-- arguments of a DataCon if possible.
collectScrut
  :: HasCallStack
  => Deferrable es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr
  -> Eval es (Either Expr Constructor, [Arg])
collectScrut = \case
  -- On a cast, we may attempt to push a TyConAppCo into the arguments of
  -- a DataCon literal.
  Cast body co -> do
    -- Perform the operation for every body in the cast.
    body' <- liftUnion body

    -- Collect the spine and arguments.
    let (spine, args) = collectThunks body'
    spine' <- case spine of
      Con lit -> pure lit
      _ -> throwE ()

    -- Only a DataCon spine may have its arguments pushed.
    dc <- case spine' of
      DataCon dc -> pure dc
      -- Any Enum DataCon suffices, as we only use its type (and all enum con
      -- have the same type).
      EnumCon _ tc | dc : _ <- tyConDataCons tc -> pure dc
      _ -> throwE ()

    -- Push the coercion into the arguments.
    (_univ, args') <- liftEff $ pushCoDataCon dc args co
    pure (Right spine', unthunk <$> args')

  -- If not a cast, we attempt to get the literal at the spine and return the
  -- arguments excluding the universal type arguments.
  expr -> do
    -- Gather the spine and its arguments.
    let (spine, args) = collectArgs expr

    -- Gather the spine as either a constructor or coercion and the number of
    -- universal arguments.
    (spine', nUniv) <- case spine of
      Con con -> pure (Right con, tyConArity $ constructorTyCon con)
      _ -> pure (Left spine, 0)

    -- Drop the universal arguments and return.
    let args' = drop nUniv args
    pure (spine', args')

-- | Push a TyConAppCo into the arguments of a DataCon.
pushCoDataCon
  :: HasCallStack
  => Deferrable es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => DataCon
  -> [Thunk]
  -> Coercion
  -> Eff es ([Type], [Thunk])
pushCoDataCon dc args co = do
  -- Check whether the outer type is a TyConAppCo.
  let tyR = coercionRKind co
  (tcR, univArgsR) <- failWith () $ splitTyConApp_maybe tyR
  unless (tcR == dataConTyCon dc) do
    throwError ()

  -- Gather information on type variables of the DataCon.
  let dcUnivVars = dataConUnivTyVars dc
  let dcExVars = dataConExTyCoVars dc

  -- Get the existential and value arguments.
  (exTys, valArgs) <- do
    let (exArgs, valArgs) = splitAtList dcExVars $ dropList dcUnivVars args
    exTys <- for exArgs \case
      -- TODO: Do we need to wrap Coercions with mkCoercionTy?
      Forced (Left ty) -> pure ty
      _ -> throwError ()
    valArgs' <- for valArgs \case
      Thunked value -> pure value
      Forced _ -> throwError ()
    pure (exTys, valArgs')

  -- Get coercions for the universal type variables.
  let univCo = decomposeCo (tyConArity tcR) co $ tyConRolesRepresentational tcR

  -- Create the new existential type arguments and the type substitution for
  -- the argument casts.
  let (psiSubst, exTys') = do
        liftCoSubstWithEx Representational dcUnivVars univCo dcExVars exTys

  -- Cast all the value arguments using the substitution.
  let argTys = scaledThing <$> dataConRepArgTys dc
  valArgs' <- for (zip valArgs argTys) \(val, ty) -> Thunked <$> thunk do
    arg <- hoistEff val
    mkCast arg $ psiSubst ty

  -- Wrap the existential type arguments back into thunks.
  let exArgs = Forced . Left <$> exTys'

  pure (univArgsR, exArgs ++ valArgs')

-- TODO: We should probably just make this a typeclass and move it to Util.
-- | Lift a result into the evaluation context.
liftEff :: Eff es a -> Eval es a
liftEff = lift

-- TODO: We can probably kill this one after we swap away from 'Eval'.
hoistEff :: Runtime a -> Eval es a
hoistEff = RuntimeT . pure . runRuntime

-- TODO: We can probably kill this one after we swap away from 'Eval'.
thunk :: Deferrable es => Eval es a -> Eff es (Runtime a)
thunk = fmap Runtime . defer . runRuntimeT

-- TODO: Remove this once we get rid of 'Eval'.
instance Deferrable es => Defer es (Eval es a) where
  type Deferred (Eval es a) = Runtime a

  defer' = Runtime . unsafeDupablePerformIO .: unEff . runRuntimeT

-- TODO: Remove this once we get rid of 'Eval'.
deferE :: Defer es a => a -> Eval es (Deferred a)
deferE = lift . defer

-- | Throw an error within the 'Eval' monadic context.
throwE
  :: HasCallStack
  => Error e :> es
  => e
  -> Eval es a
throwE = liftEff . withFrozenCallStack throwError_

-- | Throw the given error on 'Nothing' within the 'Eval' monadic context.
failWithE
  :: HasCallStack
  => Error e :> es
  => e
  -> Maybe a
  -> Eval es a
failWithE = liftEff .: withFrozenCallStack failWith

-- TODO: This should be removed at some point? Or perhaps it's usage should
-- give an error? Idk, it is a really nice utility to have when debugging stuff.
dbgE :: GHC.Outputable o => o -> Eval es ()
dbgE = liftEff . dbg
