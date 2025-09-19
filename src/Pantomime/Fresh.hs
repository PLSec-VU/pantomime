{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Fresh
  ( freshExpr
  , saturate
  ) where

import GHC.Core.Reduction (Reduction(..))
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
  , topNormaliseType_maybe
  , topNormaliseType
  )
import GHC.Types.Unique
  ( Uniquable(..)
  , getKey
  )
import GHC.Utils.Outputable
  ( Outputable (..)
  , showSDocUnsafe
  )
import GHC.Plugins
  ( Var
  , Name
  , HasOccName (..)
  , DataCon
  , HasCallStack
  , dataConTagZ
  , emptyInScopeSet
  , mkSymCo
  , isDataTyCon
  , isUnboxedTupleTyCon
  , isUnboxedSumTyCon
  , tyConDataCons_maybe
  , dataConInstArgTys
  , splitForAllTyVars
  , mkTyVarTy
  , splitFunTys
  , splitTyConApp_maybe
  , mkTyConTy
  , isNumLitTy
  )

import GHC.TypeNats
  ( SomeNat (..)
  )

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

import Data.String (IsString(..))


import Pantomime.Grisette.BitVector
  ( IntN
  )

import Pantomime.Expr
import Pantomime.Primitive.GHC qualified as Primitive
import GHC.Plugins qualified as GHC
import GHC.Core.TyCo.Compare (eqType)
import GHC.TypeLits (someNatVal)
import Control.Monad (join)
import Pantomime.Util (foldM', freshIds)
import GHC.Core.TyCo.Rep (scaledThing)
import Data.Functor ((<&>))

data Variable where
  Variable ::
    { varName :: Name
    -- ^ Root name.
    , varAccessor :: [Accessor]
    -- ^ Accessor path, note that the first entry is accessed last.
    , varType :: Type
    -- ^ Type of this variable.
    , varArgs :: [Arg]
    -- ^ Arguments which the variable depends on.
    } -> Variable

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
  :: Variable
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
  => Variable
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

freshExpr
  :: HasCallStack
  => FamInstEnvs
  -> Primitive.Types
  -> Var
  -> Arg
freshExpr famInst primTys root = go Variable
  { varName = GHC.varName root
  , varAccessor = []
  , varType = GHC.varType root
  , varArgs = []
  }
  where
    go var = do
      -- TODO: I don't like the nesting this gives. Maybe we should move these
      -- inwards somehow. The ty can actually be replaced by pattern match on
      -- the var btw.
      let ty = varType var
      let symbolic :: Solvable (ConType s) s => s
          symbolic = symbolicVar var Field
      if
        -- Haskell Primitives:
        ----------------------
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

        -- Pantomime Primitives:
        ------------------------
        -- Integer:
        | ty `eqType` mkTyConTy (Primitive.tcInteger primTys) -> do
          let value = mkInteger symbolic ty
          pure $ mkLit value

        -- IntN:
        | Just (tc, [arg]) <- splitTyConApp_maybe ty
        , tc == Primitive.tcIntN primTys
        , Just nat <- isNumLitTy $ topNormaliseType famInst arg 
        , Just (SomeNat @n _) <- someNatVal nat -> do
          -- TODO: Should we place a Cast for the type families on the inner
          -- value.
          let value = mkIntN @n symbolic ty
          pure $ mkLit value

        -- TODO: Add remaining primitives

        -- Type Family Reduction:
        -------------------------
        | Just reduction <- topNormaliseType_maybe famInst ty -> do
          let co = mkSymCo $ reductionCoercion reduction
          let ty' = reductionReducedType reduction
          let var' = var { varType = ty' }
          inner <- go var'
          mkCast inner co

        -- Algebraic Data Types:
        ------------------------
        | Just (tyCon, tyArgs) <- splitTyConApp_maybe ty
        , or
          [ isDataTyCon tyCon
          , isUnboxedTupleTyCon tyCon
          , isUnboxedSumTyCon tyCon
          ]
        , Just dataCons <- tyConDataCons_maybe tyCon -> do
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
          join $ foldM' mkUnreachable dataCons \acc dc -> do
            let scrut = tag .== fromIntegral (dataConTagZ dc)

            let fieldTys = scaledThing <$> dataConInstArgTys dc tyArgs
            let valArgs = zip [0..] fieldTys <&> \(idx, ty') -> do
                  go var
                    { varType = ty'
                    , varAccessor = Accessor dc idx : varAccessor var
                    }

            -- FIXME: This should get the proper platform size.
            let dc' = mkLit $ mkDataCon @64 dc
            let tyArgs' = pure . mkType <$> tyArgs
            let expr = mkApps dc' $ tyArgs' ++ valArgs

            pure $ mrgIte scrut expr acc

        | otherwise -> do
          dbgE ["could not create fresh value for", ppr ty]
          throwError' ()

saturate
  :: FamInstEnvs
  -> Primitive.Types
  -> Expr
  -> Eval (Expr, [(Var, Arg)])
saturate famInst primTys expr = do
  -- TODO: I don't want to generate new arguments for each inner expression. I
  -- just want arguments once. If I can do exprType for the whole thing, then
  -- perhaps I can change the type of this to (Eval Expr, [(Var, Arg)]).
  -- Actually, exprType already only uses the error part of the monad. We
  -- should just put the error part of the monad as the outer one. Then we can
  -- have the Eval for the inner Expr.
  ty <- exprType expr
  let (tvs, bty) = splitForAllTyVars ty
  let tyArgs = pure . mkType . mkTyVarTy <$> tvs
  let (atys, _) = splitFunTys bty
  let (avars, _) = freshIds (zip (repeat "arg") atys) emptyInScopeSet
  let exprArgs = freshExpr famInst primTys <$> avars
  -- FIXME: Using these tvs is not really great: We should really generate fresh
  -- ones given the current in-scope set.
  let vars = tvs ++ avars
  let args = tyArgs ++ exprArgs
  result <- mkApps expr args
  pure (result, zip vars args)
