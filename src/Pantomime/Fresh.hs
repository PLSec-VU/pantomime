{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Fresh
  ( FreshInstEnv (..)
  , freshExpr
  , freshArgs
  ) where

import GHC.Core.Reduction
  ( Reduction(..)
  , mkReduction
  , homogeniseHetRedn
  )
import GHC.Core.TyCo.Rep (scaledThing, UnivCoProvenance (..))
import GHC.Builtin.Types.Prim
  ( intPrimTy
  , int8PrimTy
  , int16PrimTy
  , int32PrimTy
  , int64PrimTy
  , wordPrimTy
  , word8PrimTy
  , word16PrimTy
  , word32PrimTy
  , word64PrimTy
  )
import GHC.Core.FamInstEnv
  ( FamInstEnvs
  , topReduceTyFamApp_maybe
  , normaliseType
  )
import GHC.Types.Unique
  ( Uniquable(..)
  , getKey
  )
import GHC.Core.TyCon.Env (TyConEnv, lookupTyConEnv)
import GHC.Utils.Outputable
  ( Outputable (..)
  , showSDocUnsafe
  )
import GHC.Plugins qualified as GHC
import GHC.Plugins
  ( Var
  , TyCon
  , Name
  , HasOccName (..)
  , DataCon
  , HasCallStack
  , InScopeSet
  , Role (..)
  , dataConTagZ
  , mkSymCo
  , isDataTyCon
  , isUnboxedTupleTyCon
  , isUnboxedSumTyCon
  , tyConDataCons_maybe
  , dataConInstArgTys
  , splitForAllTyVars
  , splitFunTys
  , splitTyConApp_maybe
  , mkTyConTy
  , isNumLitTy
  , tyVarKind
  , mkUnivCo
  , mkAppCos
  , mkReflCo
  , coreFullView
  , coercionLKind
  , coercionRKind
  , instNewTyCon_maybe
  , mkTyConAppCo
  )

import GHC.TypeLits (someNatVal)
import GHC.TypeNats (SomeNat (..))

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( Symbol
  , Solvable (..)
  , ConRep (..)
  , SExpr (..)
  , SymEq (..)
  , SimpleMergeable (..)
  , simple
  , withMetadata
  )

import Data.Functor ((<&>))
import Data.String (IsString(..))

import Pantomime.Grisette.BitVector (IntN)
import Pantomime.Expr
import Pantomime.Primitive.GHC qualified as Primitive
import Pantomime.Util (freshIds, freshTyVars, foldlBy)
import Pantomime.Result (type (!>))

data FreshInstEnv where
  FreshInstEnv ::
    { fieFam :: FamInstEnvs
    , fieUser :: TyConEnv TyCon
    , fiePrim :: Primitive.Types
    } -> FreshInstEnv

data Variable es where
  Variable ::
    { varName :: Name
    -- ^ Root name.
    , varAccessor :: [Accessor]
    -- ^ Accessor path, note that the first entry is accessed last.
    , varType :: Type
    -- ^ Type of this variable.
    , varArgs :: [Arg es]
    -- ^ Arguments which the variable depends on.
    } -> Variable es

data Accessor where
  Accessor
    :: DataCon
    -- ^ The data constructor to access.
    -> Int
    -- ^ The field number to access.
    -> Accessor

data FieldOrTag where
  Field :: FieldOrTag
  Tag :: FieldOrTag

varToSymbol
  :: Variable es
  -> FieldOrTag
  -> Symbol
varToSymbol var dst = do
  -- TODO: Clean this function up! It's super ugly!
  let name = fromString . showSDocUnsafe . ppr . occName . varName $ var
  let unique = NumberAtom . toInteger . getKey . getUnique . varName $ var
  let dst' = case dst of
        Field -> Atom "field"
        Tag -> Atom "tag"
  let accessors = flip fmap (varAccessor var) \(Accessor dc idx) -> do
        List $ fmap (NumberAtom . toInteger) [dataConTagZ dc, idx]
  let meta = List $ unique : dst' : accessors
  let ident = withMetadata name meta
  simple ident

symbolicVar
  :: Solvable (ConType s) s
  => Variable es
  -> FieldOrTag
  -> s
symbolicVar var dst = case varArgs var of
  [] -> sym $ varToSymbol var dst
  -- FIXME: We should be able to generate symbolic functions that take a number
  -- of arguments.
  -- TODO: What if arguments differ? Will this generate a different function
  -- everytime? I'm not sure how this would work, but I guess as long as the
  -- method of creation is the same it should work.
  _ -> error "Not implemented yet :("

-- TODO: This name isn't great. We really are making a symbolic expression here.
-- The freshness hinges on the freshness of the Var.
freshExpr
  :: HasCallStack
  => () !> es
  => FreshInstEnv
  -> Var
  -> EvalExpr es
freshExpr FreshInstEnv { .. } root = go Variable
  { varName = GHC.varName root
  , varAccessor = []
  , varType = GHC.varType root
  , varArgs = []
  }
  where
    -- TODO: Add note on callstack and recursion
    go var = do
      -- TODO: I don't like the nesting this gives. Maybe we should move these
      -- definitions inwards somehow.
      let ty = coreFullView $ varType var

      let symbolic :: Solvable (ConType s) s => s
          symbolic = symbolicVar var Field

      let mkReductionCast reduction = do
            let co = mkSymCo $ reductionCoercion reduction
            let var' = var { varType = reductionReducedType reduction }
            inner <- go var'
            mkCast inner co

      if
        -- Haskell Primitive:
        ---------------------
        -- FIXME: Generate proper platform size.
        | ty `eqType` intPrimTy -> pure $ mkLit (mkIntN @64 symbolic ty)
        | ty `eqType` int8PrimTy -> pure $ mkLit (mkIntN @8 symbolic ty)
        | ty `eqType` int16PrimTy -> pure $ mkLit (mkIntN @16 symbolic ty)
        | ty `eqType` int32PrimTy -> pure $ mkLit (mkIntN @32 symbolic ty)
        | ty `eqType` int64PrimTy -> pure $ mkLit (mkIntN @64 symbolic ty)
        -- FIXME: Generate proper platform size.
        | ty `eqType` wordPrimTy -> pure $ mkLit (mkWordN @64 symbolic ty)
        | ty `eqType` word8PrimTy -> pure $ mkLit (mkWordN @8 symbolic ty)
        | ty `eqType` word16PrimTy -> pure $ mkLit (mkWordN @16 symbolic ty)
        | ty `eqType` word32PrimTy -> pure $ mkLit (mkWordN @32 symbolic ty)
        | ty `eqType` word64PrimTy -> pure $ mkLit (mkWordN @64 symbolic ty)
        -- | ty `eqType` floatPrimTy -> undefined
        -- | ty `eqType` doublePrimTy -> undefined

        -- Pantomime Primitive:
        -----------------------
        -- Integer:
        | ty `eqType` mkTyConTy (Primitive.tcInteger fiePrim) -> do
          let value = mkInteger symbolic ty
          pure $ mkLit value

        -- BitVector:
        | Just (tc, [narg]) <- splitTyConApp_maybe ty
        , tc == Primitive.tcBitVector fiePrim
        , let Reduction nco nty = normaliseType fieFam Nominal narg
        , Just (SomeNat @n _) <- isNumLitTy nty >>= someNatVal -> do
          -- Coercion on the entire value for the type-level natural.
          let co = mkTyConAppCo Representational tc [mkSymCo nco]

          -- Construct the inner value and cast it.
          let inner = mkLit $ mkWordN @n symbolic (coercionLKind co)
          mkCast inner co

        -- TODO: Add remaining primitives

        -- User Interpretation:
        -----------------------
        | Just (tc, args) <- splitTyConApp_maybe ty
        , Just tc' <- lookupTyConEnv fieUser tc -> do
          -- Construct the plugin coercion
          let prov = PluginProv "pantomime user-defined"
          let tyL = mkTyConTy tc
          let tyR = mkTyConTy tc'
          let univ = mkUnivCo prov Representational tyL tyR
          let co = mkAppCos univ $ mkReflCo Nominal <$> args

          -- Create the final expression.
          mkReductionCast $ mkReduction co (coercionRKind co)

        -- Type-Family:
        ---------------
        | Just (tc, args) <- splitTyConApp_maybe ty
        , Just hreduction <- topReduceTyFamApp_maybe fieFam tc args -> do
          mkReductionCast $ homogeniseHetRedn Representational hreduction

        -- Newtype:
        -----------
        -- NOTE: It is important we first do primitive and user lookups before
        -- unfolding newtypes (i.e. the ordering of the guards are important).
        -- The primitive and user definitions diverge from the normal Haskell
        -- newtype definition. In all cases, we want the pick primitive and user
        -- definitions over newtypes.
        | Just (tc, args) <- splitTyConApp_maybe ty
        , Just (ty', co) <- instNewTyCon_maybe tc args -> do
          mkReductionCast $ mkReduction co ty'

        -- Algebraic Data Type:
        -----------------------
        | Just (tc, args) <- splitTyConApp_maybe ty
        , or $ fmap ($ tc)
          [ isDataTyCon
          , isUnboxedTupleTyCon
          , isUnboxedSumTyCon
          ]
        , Just dataCons <- tyConDataCons_maybe tc -> do
          -- FIXME: This should get the proper platform size.
          let tag = symbolicVar @(IntN S 64) var Tag

          -- TODO: This creates a long list of negated equalities for the
          -- unreachable case: tag != 0 && tag != 1 ... tag != n
          -- Instead, I wonder if it is not better to generate tag < n?
          --
          -- I guess another way to solve this would be order the Unreachable
          -- state at the end? That way, we just get a natural chain of if-then
          -- else until unreachable. I feel like this might hurt other merges
          -- though...
          --
          -- Another thing to look out for is that for enumeration TyCon, we
          -- generate.
          -- ite
          --   (tag == 0)
          --   0
          --   (ite
          --     (tag == 1)
          --     1
          --     ...)
          --
          -- But really, we should just generate the equivalent expression:
          -- tag
          --
          -- Note I skipped writing the Unreachable case in both examples.
          foldlBy mkUnreachable dataCons \acc dc -> do
            let scrut = tag .== fromIntegral (dataConTagZ dc)

            let fieldTys = scaledThing <$> dataConInstArgTys dc args
            let valArgs = zip [0..] fieldTys <&> \(idx, ty') -> go var
                  { varType = ty'
                  , varAccessor = Accessor dc idx : varAccessor var
                  }

            -- FIXME: This should get the proper platform size.
            let dc' = mkLit $ mkDataCon @64 dc
            let tyArgs = pure . mkType <$> args
            let expr = mkApps dc' $ tyArgs <> valArgs

            mrgIte scrut expr acc

        -- TODO: Throw proper error!
        | otherwise -> do
          dbgE ["could not create fresh value for", ppr ty]
          throwE ()

freshArgs
  :: HasCallStack
  => () !> es
  => FreshInstEnv
  -> Type
  -> InScopeSet
  -> ([(Var, Arg es)], InScopeSet)
freshArgs freshEnv ty scope0 = do
  -- Gather the argument types.
  let (tyVars, funTy) = splitForAllTyVars ty
  let (argTys, _resTy) = splitFunTys funTy

  -- TODO: Isn't there some infinite sequence of names that could be used
  -- instead of this?
  -- Names for the arguments.
  let names = repeat @String "arg"

  -- Create fresh type arguments.
  let kinds = zip names $ fmap tyVarKind tyVars
  let (tyArgs, scope1) = freshTyVars kinds scope0

  -- Create fresh value arguments.
  let types = zip names argTys
  let (valArgs, scope2) = freshIds types scope1

  -- Collection of all arguments.
  let args = tyArgs <> valArgs

  -- Create symbolic instance of the arguments.
  let symbolic = freshExpr freshEnv <$> args

  -- Zip the binders together with their symbolic instance.
  let binders = zip args symbolic

  -- Return the binders and the new scope.
  (binders, scope2)
