{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Pantomime.Expr
  ( Runtime
  , Variant (..)
  , Expr
  , Arg
  , Literal (..)
  , Type
  , Coercion
  , Constructor (..)

  , pprExpr
  , pprRuntime
  , pprTerm

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

  , PartialType (..)
  , exprType
  -- , collectArgs
  -- , collectScrut
  ) where

import GHC.Plugins qualified as GHC
-- import GHC.Core.Type qualified as GHC
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Ppr (pprOptCo)
import GHC.Core.Predicate (isEqPrimPred)
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
import Pantomime.Orphan.GHC ()
import Pantomime.Orphan.Grisette ()
import Pantomime.Grisette.Mergeable (impossible)
import Pantomime.Util
  ( SomeBitVec (..)
  , SymBitVec
  , BitVec
  , KnownPos
  , failWith
  , findWith
  )

import Data.Composition ((.:))
import Data.Coerce (coerce)
import Data.List ((!?))
import Data.Traversable (for)
import Data.Typeable (type (:~:) (..), eqT)

import Control.Monad ((>=>), foldM, unless, join, when)
import Control.Monad.Except (ExceptT (..))
import Control.Monad.Trans (MonadTrans (..))

import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.Cache (Cache, cache)
import Effectful.Break (break, runBreak)

import Prelude hiding (break)

-- type Eval es = RuntimeT (Eff es)

-- -- type Runtime = RuntimeT Identity

-- -- TODO: We should probably note on the fact that this is not a proper monad
-- -- transformed due to the use of UnionT. In the context where we use it, it is
-- -- completely acceptable though!
-- newtype RuntimeT m a where
--   RuntimeT' :: ExceptT Variant (UnionT m) a -> RuntimeT m a
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

-- instance MonadTrans RuntimeT where
--   lift = RuntimeT' . lift . lift

-- instance Outputable (Runtime Expr) where
--   ppr = pprRuntime pprExpr id

-- pattern Runtime :: Union (Either Variant a) -> Runtime a
-- pattern Runtime m <- (coerce -> m)
--   where
--     Runtime = coerce

runRuntime ::Runtime es a -> Union (Either (Variant es) a)
runRuntime = coerce

-- pattern RuntimeT :: m (Union (Either Variant a)) -> RuntimeT m a
-- pattern RuntimeT m <- (coerce -> m)
--   where
--     RuntimeT = coerce

-- runRuntimeT :: RuntimeT m a -> m (Union (Either Variant a))
-- runRuntimeT = coerce

-- TODO: I'm not sure if I like this name. Perhaps we can think about what other
-- options these have. Unlike the other error types, these ones don't need a
-- stack trace, as they're actually just valid values. In fact, I **really**
-- want these to merge! Perhaps something like NominalExcept/Error? Otherwise,
-- RuntimeAlt?
data Variant es where
  UB :: Variant es
  Unreachable :: Variant es
  -- TODO: Should this not contain an Expr or EvalExpr? In any case, we haven't
  -- really implemented errors yet, so we should just look into this still.
  --
  -- Future reference, we have implemented raise# using the EvalExpr for now.
  -- I guess we'll have to see if this actually makes sense, but we don't do
  -- much with errors anyway still.
  Raise :: Expr es -> Variant es
  deriving Generic
  deriving Mergeable via Default (Variant es)
  deriving EvalSym via Default (Variant es)

type Runtime es = ExceptT (Variant es) Union

type Expr es = Runtime es (Term es)

type Arg es = Expr es

-- | An effectful computation that produces an expression.
--
-- The expectation is that the result is shared via the 'Cache' effect.
type Thunk es = Eff es (Expr es)

-- TODO: I feel like a comment on this one is due: this is pretty much the main
-- data structure of the evaluator (together with Eval)!
data Term es where
  Lit
    :: Literal
    -> Term es
  Con
    :: Constructor
    -- ^ Spine of this term.
    -> [Type]
    -- ^ Universal type applications.
    -> [Type]
    -- ^ Existential type applications.
    -> [Thunk es]
    -- ^ Term applications; these are lazily evaluated.
    -> Term es
  Type
    :: Type
    -> Term es
  Coercion
    :: Coercion
    -> Term es
  Lam
    :: Type
    -- ^ Type of this term.
    -> (Thunk es -> Eff es (Expr es))
    -- ^ Closure
    -> Term es
  Cast
    :: Union (Term es)
    -> CoercionR
    -> Term es
  deriving Generic

-- TODO: Write this one!
instance Mergeable (Term es) where
  rootStrategy = undefined

instance EvalSym (Term es) where
  evalSym fill model = \case
    Lit lit -> Lit $ evalSym' lit
    Con con univ exis args -> do
      let con' = evalSym' con
      let args' = fmap evalSym' <$> args
      Con con' univ exis args'
    Type ty -> Type ty
    Coercion co -> Coercion co
    Lam ty closure -> Lam ty $ fmap evalSym' . closure
    Cast body co -> Cast (evalSym' body) co
    where
      evalSym' :: EvalSym a => a -> a
      evalSym' = evalSym fill model

instance Outputable (Term es) where
  ppr = pprTerm id

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
  => Cache :> es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => SymBitVec n
  -> Type
  -> Eff es (Expr es)
mkEnumCon tag ty = do
  -- Ensure we have an enumeration type.
  (tc, targs) <- failWith () $ splitTyConApp_maybe ty
  unless (isEnumerationTyCon tc) do
    throwError ()

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

pprTerm
  :: (SDoc -> SDoc)
  -> Term es
  -> SDoc
pprTerm addParens = \case
  Lit lit -> ppr lit
  Con con _ _ _ -> ppr con
  Type ty -> addParens $ "TYPE:" GHC.<+> ppr ty
  Coercion co -> addParens $ "CO:" GHC.<+> ppr co
  Cast expr co -> do
    let expr' = pprUnion pprTerm parens expr
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
  -- expr@App {} -> do
  --   let (fun, args) = collectArgs expr
  --   let header = pprExpr parens fun
  --   let args' = pprArg parens <$> args
  --   let body = sep args'
  --   addParens $ hang header 2 body

pprExpr
  :: (SDoc -> SDoc)
  -> Expr es
  -> SDoc
pprExpr = pprRuntime pprTerm

pprRuntime
  :: forall es a
   . Mergeable a
  => ((SDoc -> SDoc) -> a -> SDoc)
  -> (SDoc -> SDoc)
  -> Runtime es a
  -> SDoc
pprRuntime inner = do
  coerce $ pprUnion \addParens -> \case
    Left alt -> case alt of
      UB -> "UB"
      Unreachable -> "Unreachable"
      Raise expr -> "raise#" <+> pprExpr addParens expr
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
  -> Expr es
mkBitVec = mkLit . BitVec

mkInteger
  :: SymInteger
  -> Expr es
mkInteger = mkLit . Integer

mkBool
  :: SymBool
  -> Expr es
mkBool = mkLit . Bool

mkArray
  :: LiteralTypeable k
  => LiteralTypeable v
  => SymArray k v
  -> Expr es
mkArray = mkLit . Array

mkLit
  :: Literal
  -> Expr es
mkLit = pure . Lit

mkCon
  :: Constructor
  -> Expr es
mkCon con = pure $ Con con [] [] []

mkType
  :: Type
  -> Expr es
mkType = pure . Type

mkCoercion
  :: Coercion
  -> Expr es
mkCoercion = pure . Coercion

mkLam
  :: Type
  -> (Thunk es -> Eff es (Expr es))
  -> Expr es
mkLam = pure .: Lam

mkApp
  :: HasCallStack
  => Cache :> es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr es
  -> Thunk es
  -> Eff es (Expr es)
mkApp fun arg = join <$> for fun \case
  Cast body co -> do
    let body' = lift body
    (arg', rco) <- pushCoArg co arg
    expr <- mkApp body' arg'
    mkCastMCo expr rco
  Lam _ty closure -> closure arg
  -- TODO: I should give this a proper implementation.
  Con {} -> undefined
  -- _ -> liftEff do
  --   ty <- exprType fun
  --   if
  --     | isFunTy ty -> pure $ App fun (Thunked arg)
  --     | isForAllTy ty -> do
  --       forced <- forceTyCo arg
  --       pure $ App fun (Forced forced)
  --     | otherwise -> throwError ()
  _ -> throwError ()

pushCoArg
  :: HasCallStack
  => Cache :> es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => CoercionR
  -> Thunk es
  -> Eff es (Thunk es, MCoercionR)
pushCoArg co arg = if
  | let tyL = coercionLKind co
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
    arg' <- cache do
      arg' <- arg
      mkCastMCo arg' aco

    pure (arg', rco)

mkApps
  :: HasCallStack
  => Cache :> es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr es
  -> [Thunk es]
  -> Eff es (Expr es)
mkApps = foldM mkApp

mkCastMCo
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr es
  -> MCoercionR
  -> Eff es (Expr es)
mkCastMCo expr = \case
  MRefl -> pure expr
  MCo co -> mkCast expr co

mkCast
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr es
  -> CoercionR
  -> Eff es (Expr es)
mkCast expr co = runBreak do
  -- Ensure the coercion has a representational role.
  unless (coercionRole co == Representational) do
    -- FIXME: Make this a proper error.
    throwError ()

  -- Get the expression type.
  pty <- raise $ exprType expr
  ty <- case pty of
    -- Cast has no effect on non-term values, so we return early.
    Universal -> break expr
    Specific ty -> pure ty

  -- Ensure the cast can be applied to the expression.
  let kindL = coercionLKind co
  unless (eqType ty kindL) do
    -- FIXME: Make this a proper error.
    throwError ()

  -- If the coercion is reflexive, return the original expression.
  let kindR = coercionRKind co
  when (eqType kindL kindR) do
    break expr

  -- Cast every 'Term' that exists in the expression.
  pure $ expr >>= \case
    Cast body co'
      -- If the transitive coercion is reflexive, return the inner expression.
      | eqType kindR $ coercionLKind co' -> lift body
      -- Otherwise, we produce the transitive cast.
      | otherwise -> pure $ Cast body (mkTransCo co' co)

    -- NOTE: This comment was written originally inside of GHC 'mkCast'. I'm
    -- unsure what 'g' refers to (it's not in the original code either), but
    -- I'll keep the guard check here as it is probably important.
    --
    -- ```
    -- The guard here checks that g has a (~#) on both sides, otherwise
    -- 'decomposeCo' fails. Can in principle happen with unsafeCoerce.
    -- ```
    Coercion co' | isEqPrimPred kindR -> mkCoercion $ mkCoCast co' co

    term -> pure $ Cast (pure term) co

mkVariant :: Variant es -> Expr es
mkVariant = ExceptT . pure . Left

mkUnreachable :: Expr es
mkUnreachable = mkVariant Unreachable

mkUB :: Expr es
mkUB = mkVariant UB

mkRaise :: Expr es -> Expr es
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
  => Thunk es
  -> Eff es (Either Type Coercion)
forceTyCo arg = do
  arg' <- arg
  case runRuntime arg' of
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
  => Thunk es
  -> Eff es Type
forceTy = forceTyCo >=> either pure (const $ throwError ())

-- | Force an expression into a coercion using 'forceTyCo'.
forceCo
  :: HasCallStack
  => Error () :> es
  => Thunk es
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

-- | Either a 'Specific' type or a 'Universal' type that can match any type.
data PartialType where
  Universal :: PartialType
  Specific :: Type -> PartialType

-- TODO: This function deserves some clean-up! My syntax highlighter is even
-- breaking on it...
exprType
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Expr es
  -> Eff es PartialType
-- TODO: I guess we cannot always return a type: we get 'Any' type if the expr
-- is only a 'Variant'.
exprType expr = runBreak do
  -- Get the first term we can find: all terms should have the same type.
  let termM = findWith (runRuntime expr) \case
        Right inner -> Just inner
        _ -> Nothing

  -- If no 'Term' is contained, this term can be typed to any 'Type'.
  term <- maybe (break Universal) pure termM

  -- Give a specific type for the term we found.
  Specific <$> case term of
    Lit lit -> embedLitTyOf lit
    Con con univ exis args -> do
      conTy <- constructorType con
      undefined
    Type _ -> throwError ()
    Coercion co -> pure $ coercionType co
    Lam ty _ -> pure ty
    -- App fun arg -> do
    --   -- TODO: Recursive call grows callstack, fix this!
    --   fty <- exprType fun
    --   if
    --     | Just (var, rty) <- splitForAllTyCoVar_maybe fty -> do
    --       aty <- case arg of
    --         Forced (Right co) -> pure $ mkCoercionTy co
    --         Forced (Left ty) -> pure ty
    --         _ -> throwError ()
    --       let scope = mkInScopeSet $ tyCoVarsOfTypes [aty, rty]
    --       let subst = GHC.extendTCvSubst (GHC.mkEmptySubst scope) var aty
    --       pure $ GHC.substTy subst rty

    --     | Just (_, _, _, rty) <- splitFunTy_maybe fty -> pure rty

    --     | otherwise -> throwError ()
    Cast _ co -> pure $ coercionRKind co

-- -- | Collect the arguments of an application.
-- collectArgs
--   :: Expr es
--   -> (Expr es, [Thunk es (Arg es)])
-- collectArgs = second (fmap unthunk) . collectThunks

-- -- | Collect the thunks of an application.
-- collectThunks
--   :: Expr
--   -> (Expr, [Thunk])
-- collectThunks = go []
--   where
--     go args = \case
--       App fun arg -> go (arg: args) fun
--       expr -> (expr, args)

-- -- | Transform thunks into arguments.
-- --
-- -- Really, args are just always thunks. This will put forced values into thunks.
-- unthunk
--   :: Thunk
--   -> Arg
-- unthunk = \case
--   Thunked value -> value
--   Forced value -> case value of
--     Right co -> pure $ mkCoercion co
--     Left ty -> pure $ mkType ty

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
-- collectScrut
--   :: HasCallStack
--   => Deferrable es
--   => Error () :> es
--   => Context Reader BuiltInTyCon :> es
--   => Expr es
--   -> Eff es (Either (Expr es) Constructor, [Thunk es (Arg es)])
-- collectScrut = \case
--   -- On a cast, we may attempt to push a TyConAppCo into the arguments of
--   -- a DataCon literal.
--   Cast body co -> do
--     -- Perform the operation for every body in the cast.
--     body' <- liftUnion body

--     -- Collect the spine and arguments.
--     -- let (spine, args) = collectThunks body'
--     (con, univ, exis, args) <- case body' of
--       Con con univ exis args -> pure con
--       _ -> throwE ()

--     -- Only a DataCon spine may have its arguments pushed.
--     dc <- case con of
--       DataCon dc -> pure dc
--       -- Any Enum DataCon suffices, as we only use its type (and all enum con
--       -- have the same type).
--       EnumCon _ tc | dc : _ <- tyConDataCons tc -> pure dc
--       _ -> throwE ()

--     -- Push the coercion into the arguments.
--     (_univ, args') <- liftEff $ pushCoDataCon dc univ exis args co
--     pure (Right spine', unthunk <$> args')

--   -- If not a cast, we attempt to get the literal at the spine and return the
--   -- arguments excluding the universal type arguments.
--   expr -> do
--     -- Gather the spine and its arguments.
--     let (spine, args) = collectArgs expr

--     -- Gather the spine as either a constructor or coercion and the number of
--     -- universal arguments.
--     (spine', nUniv) <- case spine of
--       Con con _ _ _ -> pure (Right con, tyConArity $ constructorTyCon con)
--       _ -> pure (Left spine, 0)

--     -- Drop the universal arguments and return.
--     let args' = drop nUniv args
--     pure (spine', args')

-- | Push a TyConAppCo into the arguments of a DataCon.
pushCoDataCon
  :: HasCallStack
  => Cache :> es
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => DataCon
  -> [Type]
  -- ^ Existential type arguments.
  -> [Thunk es]
  -- ^ Term arguments.
  -> CoercionR
  -> Eff es ([Type], [Eff es (Arg es)])
pushCoDataCon dc exis args co = do
  -- Check whether the outer type is a TyConAppCo.
  let tyR = coercionRKind co
  (tcR, _univArgsR) <- failWith () $ splitTyConApp_maybe tyR
  unless (tcR == dataConTyCon dc) do
    throwError ()

  -- Gather information on type variables of the DataCon.
  let dcUnivVars = dataConUnivTyVars dc
  let dcExVars = dataConExTyCoVars dc

  -- Get coercions for the universal type variables.
  let univCo = decomposeCo (tyConArity tcR) co $ tyConRolesRepresentational tcR

  -- Create the new existential type arguments and the type substitution for
  -- the argument casts.
  let (psiSubst, exis') = do
        liftCoSubstWithEx Representational dcUnivVars univCo dcExVars exis

  -- Cast all the value arguments using the substitution.
  let argTys = scaledThing <$> dataConRepArgTys dc
  args' <- for (zip args argTys) \(thunk, ty) -> cache do
    arg <- thunk
    mkCast arg $ psiSubst ty

  pure (exis', args')
