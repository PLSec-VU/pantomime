{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

module Pantomime.Expr
  ( Eval (..)
  , Variant (..)
  , Expr (..)
  , EvalExpr
  , Arg
  , Literal (..)
  , Type
  , Coercion

  , pprExpr
  , pprArg
  , pprEval

  , mkLit
  , mkDataCon
  , mkEnumCon
  , mkIntN
  , mkWordN
  , mkInteger
  , mkBool
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

  , exprToBool
  , eqType
  , eqLit
  , exprType
  , litType
  , collectArgs
  , collectScrut

  , liftEff
  , throwE
  , failWithE
  , dbgE
  ) where

import GHC.Plugins qualified as GHC
import GHC.Core.Type qualified as GHC
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Ppr (pprOptCo)
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
  , isCoVarType
  , mkCoCast
  , isForAllTy_ty
  , coercionType
  , splitFunTy_maybe
  , splitForAllTyCoVar_maybe
  , tyConDataCons
  , dataConRepType
  , mkCoercionTy
  , tyCoVarsOfTypes
  , mkInScopeSet
  , splitTyConApp_maybe
  , dataConExTyCoVars
  , splitAtList
  , dropList
  , dataConUnivTyVars
  , decomposeCo
  , tyConArity
  , tyConFamilySize
  , tyConRolesRepresentational
  , liftCoSubstWithEx
  , dataConRepArgTys
  , boolTyCon
  , trueDataCon
  , falseDataCon
  )

import GHC.TypeNats (KnownNat)
import GHC.Generics (Generic)
import GHC.Stack (withFrozenCallStack)

import Grisette.Unified (EvalModeTag (..))
import Grisette qualified (LogicalOp (..))
import Grisette
  ( Union
  , SymBool
  , SymInteger
  , SymEq (..)
  , SymOrd (..)
  , LogicalOp ((.&&))
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
  , LinkedRep
  , ConRep (..)
  , wrapStrategy
  , liftUnion
  , mrgIf
  , pattern Single
  , pattern If
  )
-- TODO: Change import once we fully integrate SymArray into grisette! Right
-- now, we still need to touch these internal things...
import Grisette.Internal.SymPrim.SymArray (SymArray)
import Grisette.Internal.SymPrim.Prim.Term (SupportedNonFuncPrim (..))

import Pantomime.Orphan.Grisette ()
import Pantomime.Orphan.GHC ()
import Pantomime.Grisette.UnionT
import Pantomime.Grisette.SomeBV (SomeBV (..))
import Pantomime.Grisette.Mergeable (NoEval1 (..), DynIdx (..), impossible)
import Pantomime.Grisette.BitVector (IntN, WordN)
import Pantomime.Util (failWith, dbg)

import Data.Composition ((.:))
import Data.Coerce (coerce)
import Data.List ((!?), uncons)
import Data.Traversable (for)
import Data.Typeable (type (:~:) (..), Typeable, eqT)

import Control.Arrow (Arrow(..))
import Control.Monad.Except (ExceptT (..))
import Control.Monad ((>=>), foldM, unless)
import Control.Monad.Trans (MonadTrans(..))

import Effectful
import Effectful.Error.Static

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
newtype Eval es a where
  Eval :: ExceptT (Variant es) (UnionT (Eff es)) a -> Eval es a
  deriving Functor
  deriving Applicative
  deriving Monad
  deriving TryMerge
  deriving Mergeable
  deriving Mergeable1
  deriving SimpleMergeable
  deriving SimpleMergeable1
  deriving SymBranching
  deriving EvalSym via (EvalEvalSym es a)
  deriving EvalSym1 via (EvalEvalSym es)

-- | SymEval coercion for inner value of 'Eval' monad, useful for derivations.
type EvalEvalSym es = ExceptT (Variant es) (UnionT (NoEval1 (Eff es)))

-- TODO: I'm not sure if I like this name. Perhaps we can think about what other
-- options these have. Unlike the other error types, these ones don't need a
-- stack trace, as they're actually just valid values. In fact, I **really**
-- want these to merge! Perhaps something like NominalExcept/Error?
data Variant es where
  UB :: Variant es
  Unreachable :: Variant es
  -- TODO: Should this not contain an Expr or EvalExpr? In any case, we haven't
  -- really implemented errors yet, so we should just look into this still.
  --
  -- Future reference, we have implemented raise# using the EvalExpr for now.
  -- I guess we'll have to see if this actually makes sense, but we don't do
  -- much with errors anyway still.
  Raise :: EvalExpr es -> Variant es
  deriving Generic
  deriving Mergeable via Default (Variant es)
  deriving EvalSym via Default (Variant es)

-- TODO: I feel like a comment on this one is due: this is pretty much the main
-- data structure of the evaluator (together with Eval)!
data Expr es where
  Lit
    :: Literal
    -> Expr es
  Type
    :: Type
    -> Expr es
  Coercion
    :: Coercion
    -> Expr es
  Lam
    :: Type
    -- ^ Expression type
    -> (Arg es -> EvalExpr es)
    -- ^ Closure
    -> Expr es
  -- TODO: I guess the only time App is used is for DataCon. Maybe having it
  -- in here is too general and it should just be part of DataCon? I guess
  -- technically a Cast might also be at the root no? Whilst we do fold casts
  -- over FunCo, we don't actually handle the case where a Cast occurs and it is
  -- not over a FunCo as root right now. I'll have to think about what's best.
  --
  -- I guess if the cast is not a FunCo or ForAllCo, at some point the execution
  -- will halt anyway once we want to pattern match on it though. Maybe indeed,
  -- only DataCon needs arguments.
  App
    :: Expr es
    -> Thunk es
    -> Expr es
  Cast
    :: Union (Expr es)
    -> CoercionR
    -> Expr es
  deriving Generic
  deriving Mergeable via Default (Expr es)

-- | Expressions within the evaluation context. You may also think of these as
-- thunks. It is expected that the spine of this expression is never a 'Type' or
-- 'Coercion'.
type EvalExpr es = Eval es (Expr es)

-- | Like 'EvalExpr', this may be considered a thunk. Unlike 'EvalExpr', this is
-- an expression that may appear in the argument position. This entails that
-- it may be a 'Type' or 'Coercion' in the spine.
type Arg es = EvalExpr es

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
data Thunk es where
  Thunked :: Arg es -> Thunk es
  Forced :: Either Type Coercion -> Thunk es
  deriving Generic
  deriving Mergeable via Default (Thunk es)

-- TODO: Since we have this whole user-axiom/interpretation scheme now, we
-- really don't need to track types for primitive literals (i.e. the
-- non-constructor ones). That is, there should only be one type for each of
-- these as even Haskell primitives should just go through the user-axioms at
-- this point. As such, we should change this at some point! The first step
-- would be to remove the built-in support for Haskell primitives. From there,
-- it is probably relatively simple the get rid of the types!
data Literal where
  -- TODO: I think it makes sense to place the universal type arguments of a
  -- DataCon inside of the literal.
  -- TODO: Does it not make sense to seperate enumeration DataCon from normal
  -- DataCon? I.e. we can have the following two cases:
  -- DataCon :: DataCon -> Literal
  -- EnumCon :: KnownNat n => SymIntN n -> TyCon -> Literal
  --
  -- If we do it this way, we don't need a manual implementation of Mergeable.
  -- (Actually, I guess we still do because of the existential on the bitvector)
  -- Also, there are many edge-cases right now in the code for when it is, or is
  -- not an EnumCon. In this way, the distinction is a little bit more explicit!
  -- I think we should change this!
  --
  -- TODO: Changing to the above EnumCon/DataCon split, does it make sense to
  -- split constructors from the other literals. They're used in a lot of
  -- different positions and sometimes it just makes sense to not want to reason
  -- about the possibility of primitive values. Perhaps we could just add a
  -- 'Con' field to 'Expr'? In this case, perhaps we want to also just attach
  -- their applications to them as well since we don't actually use App for
  -- anything else anyway?
  DataCon
    :: DataCon
    -> Literal
  EnumCon
    :: KnownNat n
    => IntN S n
    -> TyCon
    -> Literal
  -- TODO: Does it make sense to differentiate between IntN and WordN? I think
  -- the solver just has a single bitvector. This just seems like it adds
  -- maintanence burden without actually adding anything...
  -- We should make a single BitVector field!
  -- I also think we should switch back to the grisette WordN with this. I say
  -- this because it eases up the constraints when trying to fit these into an
  -- Array. That is, the SMT only allows bitvectors with a bitsize larger than
  -- 0. Any user that want to support zero-sized bitvectors should just
  -- implement the bitvector at the frontend in the way we now did for the
  -- backend.
  Int
    :: KnownNat n
    => IntN S n
    -> Type
    -> Literal
  Word
    :: KnownNat n
    => WordN S n
    -> Type
    -> Literal
  Integer
    :: SymInteger
    -> Type
    -> Literal
  Bool
    :: SymBool
    -> Type
    -> Literal
  Array ::
     ( SupportedNonFuncSymPrim k
     , SupportedNonFuncSymPrim v
     , Typeable k
     , Typeable v
     )
    => SymArray k v
    -> Type
    -> Literal

-- TODO: I guess I should move this thing somewhere. I only have this as I need
-- use it in a 'Dict' once. Still, I don't like it particularly. Also, I think
-- Grisette doesn't expose SupportedNonFuncPrim. It is only visible in an
-- internal module and other users (like SymGeneralFun) actually have it stored
-- locally. To be fair though, that's honestly just bad practise.
class
  ( SupportedNonFuncPrim (ConType a)
  , LinkedRep (ConType a) a
  ) => SupportedNonFuncSymPrim a
instance
  ( SupportedNonFuncPrim (ConType a)
  , LinkedRep (ConType a) a
  ) => SupportedNonFuncSymPrim a

instance Mergeable Literal where
  rootStrategy = SortedStrategy
    (\case
      DataCon {} -> 0 :: Int
      EnumCon {} -> 1
      Int {} -> 2
      Word {} -> 3
      Integer {} -> 4
      Bool {} -> 5
      Array {} -> 6)
    \case
      0 -> wrapStrategy
        rootStrategy
        DataCon
        \case DataCon dc -> dc ; _ -> impossible

      1 -> wrapStrategy
        rootStrategy
        (\case (SomeBV tag, tc) -> EnumCon tag tc)
        \case EnumCon tag tc -> (SomeBV tag, tc) ; _ -> impossible

      2 -> wrapStrategy
        rootStrategy
        (\case (SomeBV value, ty) -> Int value ty)
        \case Int value ty -> (SomeBV value, ty) ; _ -> impossible

      3 -> wrapStrategy
        rootStrategy
        (\case (SomeBV value, ty) -> Word value ty)
        \case Word value ty -> (SomeBV value, ty) ; _ -> impossible

      4 -> wrapStrategy
        rootStrategy
        (\case (value, ty) -> Integer value ty)
        \case Integer value ty -> (value, ty) ; _ -> impossible

      5 -> wrapStrategy
        rootStrategy
        (\case (value, ty) -> Bool value ty)
        \case Bool value ty -> (value, ty) ; _ -> impossible

      6 -> SortedStrategy
        (\case
          Array @k @v _ _ -> do
            let idxK = DynIdx @k @SupportedNonFuncSymPrim
            let idxV = DynIdx @v @SupportedNonFuncSymPrim
            (idxK, idxV)
          _ -> impossible)
        \(DynIdx @k, DynIdx @v) -> wrapStrategy @(SymArray k v, Type)
          rootStrategy
          (\case (value, ty) -> Array value ty)
          \case
            Array @k' @v' value ty
              | Just Refl <- eqT @k @k'
              , Just Refl <- eqT @v @v' -> (value, ty)
            _ -> impossible

      _ -> impossible

instance EvalSym (Expr es) where
  evalSym fill model = \case
    Lit lit -> Lit $ evalSym' lit
    Type ty -> Type ty
    Coercion co -> Coercion co
    Lam ty closure -> Lam ty \arg -> evalSym' (closure arg)
    App fun arg -> App (evalSym' fun) (evalSym' arg)
    Cast body co -> Cast (evalSym' body) co
    where
      evalSym' :: EvalSym a => a -> a
      evalSym' = evalSym fill model

instance EvalSym Literal where
  evalSym fill model = \case
    DataCon dc -> DataCon dc
    EnumCon tag tc -> EnumCon (evalSym' tag) tc
    Int value ty -> Int (evalSym' value) ty
    Word value ty -> Word (evalSym' value) ty
    Integer value ty -> Integer (evalSym' value) ty
    Bool value ty -> Bool (evalSym' value) ty
    Array value ty -> Array (evalSym' value) ty
    where
      evalSym' :: EvalSym a => a -> a
      evalSym' = evalSym fill model

instance EvalSym (Thunk es) where
  evalSym fill model = \case
    Thunked value -> Thunked $ evalSym fill model value
    Forced value -> Forced value

pprExpr
  :: (SDoc -> SDoc)
  -> Expr es
  -> Eff es SDoc
pprExpr addParens = \case
  Lit lit -> pure $ ppr lit
  Type ty -> pure $ "@" GHC.<> ppr ty
  Coercion co -> pure $ "@~" GHC.<> ppr co
  Cast expr co -> do
    expr' <- pprUnion expr parens pprExpr
    pure . addParens $ sep
      [ expr'
      , "`cast`" <+> pprOptCo co
      ]
  -- TODO: This one is a bit more difficult. Really the only way to print a
  -- lambda is to provide it with fresh arguments. The problem is that we need
  -- a lot more context for printing in that way.
  --
  -- Since we actually changed the underyling monad in Eval to allow for more
  -- effects, we could actually implement this now. :) The only annoying thing
  -- is the dependency on the fresh variable generation here...
  Lam {} -> pure "TODO lambda"
    -- (result, args) <- saturateLam @64 $ mkExpr expr
    -- let bndrs = fst <$> args
    -- let bndr = "\\" <+> sep (ppr <$> bndrs) <+> GHC.arrow
    -- body <- pprExpr id result
    -- pure . addParens $ hang bndr 2 body
  expr@App {} -> do
    let (fun, args) = collectArgs expr
    header <- pprExpr parens fun
    args' <- for args $ pprArg parens
    let body = sep args'
    pure . addParens $ hang header 2 body

pprArg
  :: (SDoc -> SDoc)
  -> Arg es
  -> Eff es SDoc
pprArg addParens = pprEval addParens pprExpr

pprEval
  :: forall a es
   . Mergeable a
  => (SDoc -> SDoc)
  -> ((SDoc -> SDoc) -> a -> Eff es SDoc)
  -> Eval es a
  -> Eff es SDoc
pprEval addParens f m = do
  value :: Union (Either (Variant es) a) <- coerce m
  pprUnion value addParens \p -> \case
    Left alt -> case alt of
      UB -> pure "UB"
      Unreachable -> pure "Unreachable"
      Raise expr -> ("raise#" <+>) <$> pprArg p expr
    Right expr -> f p expr

pprUnion
  :: Mergeable a
  => Union a
  -> (SDoc -> SDoc)
  -> ((SDoc -> SDoc) -> a -> Eff es SDoc)
  -> Eff es SDoc
pprUnion union addParens inner = case union of
  Single value -> inner addParens value
  If scrut true false -> do
    -- Vertically concatenate using ($+$).
    let vcat' = foldl' @[] ($+$) GHC.empty

    -- Hang that always aligns vertically.
    let hang' d1 n d2 = vcat' [d1, nest n d2]

    -- Pretty print branches.
    true' <- pprUnion true parens inner
    false' <- pprUnion false parens inner

    -- Hange the branches below an if-then-else.
    pure . addParens . hang' "ite" 2 $ vcat'
      [ text $ show scrut
      , true'
      , false'
      ]

instance Outputable Literal where
  ppr = \case
    -- TODO: This should output the tag directly if concrete. If not and this is
    -- an enumeration TyCon, we should emit a tagToEnum# apply to the value. If
    -- this is not an enumeration TyCon, then the tag is invalid. We should
    -- probably print some sort of error message in that case.
    DataCon dc -> ppr dc
    EnumCon @n tag tc
      | Just tag' <- toCon @_ @(IntN C n) tag 
      , Just dc <- tyConDataCons tc !? fromIntegral tag' -> ppr dc
      -- TODO: Technically this print is wrong as the type application should be
      -- the whole type, not just the TyCon.
      | otherwise -> "tagToEnum#" <+> "@" GHC.<> ppr tc <+> ppr (SomeBV tag)
    -- TODO: We are printing the grisette primitives using show which is
    -- oblivious to indentation. We should make an actual pretty printer for
    -- symbolic variables. Ideally, the variable names get the pretty printing
    -- that is similar to how their naming works in the fresh variable
    -- generation.
    Int value ty -> ppr (SomeBV value) <+> "::" <+> ppr ty
    Word value ty -> ppr (SomeBV value) <+> "::" <+> ppr ty
    Integer value ty -> text (show value) <+> "::" <+> ppr ty
    Bool value ty -> text (show value) <+> "::" <+> ppr ty
    Array value ty -> text (show value) <+> "::" <+> ppr ty

mkLit
  :: Literal
  -> Expr es
mkLit = Lit

mkDataCon
  :: forall n
   . KnownNat n
  => DataCon
  -> Literal
mkDataCon dc = if
  | let tc = dataConTyCon dc
  , isEnumerationTyCon tc -> do
    let tag = fromIntegral . dataConTagZ $ dc
    EnumCon @n tag tc
  | otherwise -> DataCon dc

mkEnumCon
  :: forall n es
   . KnownNat n
  => Error () :> es
  => IntN S n
  -> Type
  -> EvalExpr es
mkEnumCon tag ty = do
  -- Ensure we have an enumeration type.
  (tc, targs) <- failWithE () $ splitTyConApp_maybe ty
  unless (isEnumerationTyCon tc) do
    throwE ()

  -- TODO: I don't think it makes sense to put this check here. Really, we only
  -- get UB if we actually try to use the tag for a pattern match. Already, we
  -- use UB in case expressions, so I think this could just be removed.
  --
  -- If we do, do make sure to adjust exprToBool accordingly: we actually do
  -- need to assert no UB occurred!
  -- Check to ensure we have a proper tag.
  let upper = fromIntegral $ tyConFamilySize tc
  let inBounds = 0 .<= tag .&& tag .< upper

  -- Construct the data constructor and its type arguments.
  let dc = mkLit $ EnumCon tag tc
  let targs' = pure . mkType <$> targs
  let expr = mkApps dc targs'

  -- The expression is UB if it the tag is not within bounds.
  mrgIf inBounds expr mkUB

mkIntN
  :: KnownNat n
  => IntN S n
  -> Type
  -> Literal
mkIntN = Int

mkWordN
  :: KnownNat n
  => WordN S n
  -> Type
  -> Literal
mkWordN = Word

mkInteger
  :: SymInteger
  -> Type
  -> Literal
mkInteger = Integer

mkBool
  :: SymBool
  -> Type
  -> Literal
mkBool = Bool

mkType
  :: Type
  -> Expr es
mkType = Type

mkCoercion
  :: Coercion
  -> Expr es
mkCoercion = Coercion

mkLam
  :: Type
  -> (Arg es -> EvalExpr es)
  -> Expr es
mkLam = Lam

mkApp
  :: HasCallStack
  => Error () :> es
  => Expr es
  -> Arg es
  -> EvalExpr es
mkApp fun arg = case fun of
  Cast body co -> do
    (arg', rco) <- pushCoArg co arg
    body' <- liftUnion body
    expr <- mkApp body' arg'
    mkCastMCo expr rco
  Lam _ty closure -> closure arg
  _ -> do
    ty <- liftEff $ exprType fun
    if
      | isFunTy ty -> pure $ App fun (Thunked arg)
      | isForAllTy ty -> do
        forced <- liftEff $ forceTyCo arg
        pure $ App fun (Forced forced)
      | otherwise -> throwE ()

pushCoArg
  :: HasCallStack
  => Error () :> es
  => CoercionR
  -> Arg es
  -> Eval es (Arg es, MCoercionR)
pushCoArg co arg = if
  | tyL <- coercionLKind co
  , isForAllTy_ty tyL -> do
    -- The argument needs to be a type. As such, we can force it.
    ty <- liftEff $ forceTy arg

    -- Attempt to push the coercion into the type argument.
    (ty', rco) <- failWithE () $ pushCoTyArg co ty

    -- Return the type argument and result coercion.
    pure (pure $ mkType ty', rco)

  | otherwise -> do
    -- Attempt to split the coercion into an argument and result coercion.
    (aco, rco) <- failWithE () $ pushCoValArg co

    -- Cast the argument and return the result coercion.
    let arg' = arg >>= flip mkCastMCo aco
    pure (arg', rco)

mkApps
  :: HasCallStack
  => Error () :> es
  => Expr es
  -> [Arg es]
  -> EvalExpr es
mkApps = foldM mkApp

mkCastMCo
  :: HasCallStack
  => Error () :> es
  => Expr es
  -> MCoercionR
  -> EvalExpr es
mkCastMCo expr = \case
  MRefl -> pure expr
  MCo co -> mkCast expr co

mkCast
  :: HasCallStack
  => Error () :> es
  => Expr es
  -> CoercionR
  -> EvalExpr es
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
    -- A reflexive cast is a no-op and thus may be removed immediately.
    _ | isReflexiveCo co -> pure expr

    -- TODO: This is a recursive call of HasCallStack, I should capture it in a
    -- closure as to not blow it up instead!
    Cast body co' -> do
      body' <- liftUnion body
      mkCast body' $ mkTransCo co' co

    -- NOTE: This comment was written originally inside of GHC 'mkCast'. I'm
    -- unsure what 'g' refers to (it's not in the original code either), but
    -- I'll keep the guard check here as it is probably important.
    --
    -- ```
    -- The guard here checks that g has a (~#) on both sides, otherwise
    -- 'decomposeCo' fails. Can in principle happen with unsafeCoerce.
    -- ```
    Coercion co' | isCoVarType $ coercionRKind co -> do
      pure $ mkCoercion (mkCoCast co' co)

    _ -> pure $ Cast (pure expr) co

mkVariant :: Variant es -> Eval es a
mkVariant = Eval . ExceptT . pure . Left

mkUnreachable :: Eval es a
mkUnreachable = mkVariant Unreachable

mkUB :: Eval es a
mkUB = mkVariant UB

mkRaise :: EvalExpr es -> Eval es a
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
  => Arg es
  -> Eff es (Either Type Coercion)
forceTyCo arg = do
  -- Simply pass an already existing error, if possible.
  arg' :: Union (Either (Variant es) (Expr es)) <- coerce arg

  case arg' of
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
  => Arg es
  -> Eff es Type
forceTy = forceTyCo >=> either pure (const $ throwError ())

-- | Force an expression into a coercion using 'forceTyCo'.
forceCo
  :: HasCallStack
  => Error () :> es
  => Arg es
  -> Eff es Coercion
forceCo = forceTyCo >=> either (const $ throwError ()) pure

-- | Convert an expression of type Bool to a symbolic boolean.
exprToBool
  :: HasCallStack
  => Error () :> es
  => Expr es
  -> Eval es SymBool
exprToBool = \case
  Lit (EnumCon tag tc) | tc == boolTyCon -> do
    -- DataCon are checked at creation for correctness. Hence, we can simply
    -- cast the bit value.
    -- TODO: This above statement might not be true at some point. Really, we
    -- should check at usage site as it doesn't make sense to check at creation:
    -- creating a bad dataconstructor doesn't result in UB if we don't branch
    -- on it!
    -- TODO: I noticed that Grisette has trouble with reasoning about bit-casts
    -- when compared to just If statements. With this in mind, I think it makes
    -- more sense to just do the if statement here!
    --
    -- Okay, did it now, but it really looks ugly. Maybe deserves some clean-up.
    let eqCon dc = tag .== fromIntegral (dataConTagZ dc)
    mrgIf (eqCon trueDataCon)
      (pure Grisette.true)
      (mrgIf (eqCon falseDataCon)
        (pure Grisette.false)
        mkUB)

  _ -> throwE ()

-- | Equivalence between literals.
--
-- NOTE: This only handles cases that may occur in a case expression.
eqLit
  :: HasCallStack
  => Error () :> es
  => Literal
  -> Literal
  -> Eff es SymBool
eqLit = \cases
  (DataCon ldc) (DataCon rdc)
    | dataConTyCon ldc == dataConTyCon rdc -> pure $ toSym (ldc == rdc)
  (EnumCon @l ltag ltc) (EnumCon @r rtag rtc)
    | ltc == rtc
    , Just Refl <- eqT @l @r -> pure $ ltag .== rtag
  (Int @l lval lty) (Int @r rval rty) 
    | eqType lty rty
    , Just Refl <- eqT @l @r -> pure $ lval .== rval
  (Word @l lval lty) (Word @r rval rty) 
    | eqType lty rty
    , Just Refl <- eqT @l @r -> pure $ lval .== rval
  _ _ -> throwError ()

-- TODO: This function deserves some clean-up! My syntax highlighter is even
-- breaking on it...
exprType
  :: HasCallStack
  => Error () :> es
  => Expr fs
  -> Eff es Type
exprType = \case
  Lit lit -> litType lit
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

litType
  :: Error () :> es
  => Literal
  -> Eff es Type
litType = \case
  DataCon dc -> pure $ dataConRepType dc
  EnumCon _ tc -> do
    (dc, _) <- failWith () $ uncons (tyConDataCons tc)
    pure $ dataConRepType dc
  Int _ ty -> pure ty
  Word _ ty -> pure ty
  Integer _ ty -> pure ty
  Bool _ ty -> pure ty
  Array _ ty -> pure ty

-- | Collect the arguments of an application.
collectArgs
  :: Expr es
  -> (Expr es, [Arg es])
collectArgs = second (fmap unthunk) . collectThunks

-- | Collect the thunks of an application.
collectThunks
  :: Expr es
  -> (Expr es, [Thunk es])
collectThunks = go []
  where
    go args = \case
      App fun arg -> go (arg: args) fun
      expr -> (expr, args)

-- | Transform thunks into arguments.
--
-- Really, args are just always thunks. This will put forced values into thunks.
unthunk
  :: Thunk es
  -> Arg es
unthunk = \case
  Thunked value -> value
  Forced value -> case value of
    Right co -> pure $ mkCoercion co
    Left ty -> pure $ mkType ty

-- | Collect the arguments of a scrutinee.
--
-- This will drop any universal type applications as these are not necessary for
-- pattern matching. Additionally, this will push a TyCon Coercion into the
-- arguments of a DataCon if possible.
collectScrut
  :: HasCallStack
  => Error () :> es
  => Expr es
  -> Eval es (Either Coercion Literal, [Arg es])
collectScrut = \case
  -- On a cast, we may attempt to push a TyConAppCo into the arguments of
  -- a DataCon literal.
  Cast body co -> do
    -- Perform the operation for every body in the cast.
    body' <- liftUnion body

    -- Collect the spine and arguments.
    let (spine, args) = collectThunks body'
    spine' <- case spine of
      Lit lit -> pure lit
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

    -- Gathers the number of universal arguments of a literal.
    let nUnivLit = \case
          DataCon dc -> tyConArity $ dataConTyCon dc
          EnumCon _ tc -> tyConArity tc
          -- TODO: Use or pattern once we bump the GHC version.
          Int {} -> 0
          Word {} -> 0
          Integer {} -> 0
          Bool {} -> 0
          -- TODO: I'm not sure if this 2 is actually correct. I'll have to
          -- double check!
          Array {} -> 2

    -- Gather the spine as either a literal or coercion and the number of
    -- universal arguments.
    (spine', nUniv) <- case spine of
      Lit lit -> pure (Right lit, nUnivLit lit)
      Coercion co -> pure (Left co, 0)
      _ -> throwE ()

    -- Drop the universal arguments and return.
    let args' = drop nUniv args
    pure (spine', args')

-- | Push a TyConAppCo into the arguments of a DataCon.
pushCoDataCon
  :: HasCallStack
  => Error () :> es
  => DataCon
  -> [Thunk es]
  -> Coercion
  -> Eff es ([Type], [Thunk es])
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
  let (psiSubst, exTys')
        = liftCoSubstWithEx Representational dcUnivVars univCo dcExVars exTys

  -- Cast all the value arguments using the substitution.
  let argTys = scaledThing <$> dataConRepArgTys dc
  let castArg arg ty = arg >>= flip mkCast (psiSubst ty)
  let valArgs' = Thunked <$> zipWith castArg valArgs argTys

  -- Wrap the existential type arguments back into thunks.
  let exArgs = Forced . Left <$> exTys'

  pure (univArgsR, exArgs ++ valArgs')

-- | Lift a result into the evaluation context.
liftEff :: Eff es a -> Eval es a
liftEff = Eval . lift . lift

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
