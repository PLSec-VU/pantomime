{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Axiom
  ( PluginAxioms (..)
  , PluginAxiomsR (..)
  , TypeAxiomsR
  , TermAxiomsR
  , resolvePluginAxioms
  ) where

import Language.Haskell.TH qualified as TH

import GHC.Core.TyCo.Rep (UnivCoProvenance(..))
import GHC.Core.TyCon.Env (TyConEnv, mkTyConEnv)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Data.TrieMap (TrieMap (..), insertTM)
import GHC.Plugins
  ( Unfolding (..)
  , InlineSpec (..)
  , TyCon (..)
  , Name
  , Id
  , CoreExpr
  , CoreProgram
  , Role (..)
  , Expr (..)
  , Var (..)
  , InlinePragma (..)
  , TypeOrConstraint (..)
  , mkTyConTy
  , mkUnivCo
  , dataConWorkId
  , mkApps
  , mkCast
  , mkSymCo
  , exprType
  , hasCoreUnfolding
  , realIdUnfolding
  , idInlinePragma
  , classDataCon
  , typeKind
  , unitExpr
  , unrestricted
  , emptyInScopeSet
  , sORTKind_maybe
  )
import GHC.Utils.Outputable (Outputable (..), IsDoc (..), hang)

import GHC.Exts (IsList(..))

import Control.Monad ((>=>), unless)
import Control.Applicative (Alternative (..))

import Data.Data (Data)
import Data.Map (Map)
import Data.Typeable (Typeable)
import Data.Traversable (for)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.Context

import Pantomime.BuiltIn (Embeddable)
import Pantomime.Unification (resolveInstancesWith)
import Pantomime.Util (foldM', freshId, failWith)

-- TODO: We're switching away from using 'Coercible' as it requires same runtime
-- kinded types: something we don't care about within the evaluator. Instead,
-- we provide a custom typeclass. The comments should mirror this!
-- | User axioms only visible to the plugin.
--
-- The kinds and types of the mapped terms should match up exactly. The
-- exception is that type-level axioms will be used to instantiate requirements
-- of 'Embeddable' on any term-level axiom.
--
-- # Example
--
-- Suppose the user has some bitvector type called 'IntN'.
--
-- > type IntN (n :: Nat) = ...
--
-- The user supplies the following mapping:
--
-- > IntN |-> BitVec
--
-- This roughly says that the user wants to use the underlying bitvector
-- representation 'BitVec'. 'BitVec' is treated as a primitive within the plugin
-- and is implemented using the respective SMT theory. A mapping between
-- non-primitive types is also allowed (or any mixing of these, use type aliases
-- for this).
--
-- Now, a user has some functions that operate on 'IntN'. These of course
-- require a mapping to the their respective operation on 'BitVec'. Before
-- anything, a user needs to ensure that **ALL** operations on 'IntN' are
-- through functions marked as 'OPAQUE' and that it's constructor is not
-- exported. This is to ensure correctness within the evaluator, as otherwise
-- representational equivalence is broken.
--
-- With this in mind, the following will illustrate how to write an
-- interpretation. Suppose we have an addition function for 'IntN' values.
--
-- > {-# OPAQUE plusIntN #-}
-- > plusIntN :: KnownNat n => IntN n -> IntN n -> IntN n
--
-- We can write an interpretation for this using the addition as provided by
-- 'BitVec'. The importance lies in using a coercion 'Coercible IntN BitVec'.
--
-- > plusInterp
-- >   :: Coercible IntN BitVec
-- >   => KnownNat n
-- >   => IntN n
-- >   -> IntN n
-- >   -> IntN n
-- > plusInterp = go
-- >   where
-- >     go :: bv ~ BitVec => bv n -> bv n -> bv n
-- >     go = coerce plusIntN
--
-- Note, the where clause is only to trick Haskell into allowing the coercion
-- to appear at the top level. With this defintion in place, we supply the
-- appropriate mapping:
--
-- > plusIntN |-> plusInterp
--
-- Of course, the types for 'plusIntN' and 'plusInterp' do not match up
-- one-to-one. That is, to complete the interpretation, we supply 'plusInterp'
-- with the user-supplied coercion that 'Coercible IntN BitVec'. Afterwards, the
-- types match up and the function is a valid interpretation.
data PluginAxioms where
  PluginAxioms ::
    { typeAxioms :: Map TH.Name TH.Name
    -- ^ Type-level representational equivalence axioms.
    --
    -- Both the key and value of these mappings should be resolvable to 'TyCon'.
    -- One may think about this as providing an instance 'Coercible' to just the
    -- plugin between the given 'TyCon'. This instance is used within the solver
    -- when constructing fresh symbolic values and when resolving instances
    -- for term-axioms.
    -- TODO: Term axioms should allow for recursive definitions also. It
    -- probably won't be used much, but it would be good! I guess we would want
    -- a 'Bind' from GHC, but for template haskell names.
    , termAxioms :: [(TH.Name, TH.Name)]
    -- ^ Term-level representational equivalence axioms.
    --
    -- Both the key and value of these mappings should be resolvable to 'Id'.
    -- This can be used to operate on types that have user-provided equivalence
    -- axioms via 'typeAxioms'. The types should match exactly between both
    -- 'Id's, with the exception of 'Coercible' instances that may be resolved
    -- using the 'typeAxioms'.
    --
    -- Note that this is a list because the ordering of the definitions does
    -- matter: any later definitions may use ones defined earlier. Duplicate
    -- definitions are considered an error.
    } -> PluginAxioms
  deriving (Show, Data, Typeable)

instance Semigroup PluginAxioms where
  (<>) l r = PluginAxioms
    { typeAxioms = typeAxioms l <> typeAxioms r
    , termAxioms = termAxioms l <> termAxioms r
    }

instance Monoid PluginAxioms where
  mempty = PluginAxioms
    { typeAxioms = mempty
    , termAxioms = mempty
    }

type TypeAxiomsR = TyConEnv TyCon

-- TODO: I guess these might be better suited as CoreBind no?
type TermAxiomsR = [(Id, CoreExpr)]

-- TODO: I think it would be good to have type synonyms for both of these fields
-- as we use them independently as well.
-- | Fully resolved plugin axioms. These may be used as-is by the solver.
data PluginAxiomsR where
  PluginAxiomsR ::
    { typeAxiomsR :: TypeAxiomsR
    -- ^ Type-level axioms, mainly used to construct symbolic values.
    , termAxiomsR :: TermAxiomsR
    -- ^ Term-level axioms, these already have their 'Coercible' instances
    -- resolved by the type-axioms, where applicable.
    --
    -- This may be used to extend substitution environments.
    } -> PluginAxiomsR
    deriving (Data, Typeable)

instance Outputable PluginAxiomsR where
  ppr PluginAxiomsR { .. } = hang "PluginAxiomsR" 2 $ vcat
    [ hang "Type Axioms:" 2 $ ppr typeAxiomsR
    , hang "Term Axioms:" 2 $ ppr termAxiomsR
    ]

instance Semigroup PluginAxiomsR where
  (<>) l r = PluginAxiomsR
    { typeAxiomsR = typeAxiomsR l <> typeAxiomsR r
    , termAxiomsR = termAxiomsR l <> termAxiomsR r
    }

instance Monoid PluginAxiomsR where
  mempty = PluginAxiomsR
    { typeAxiomsR = mempty
    , termAxiomsR = mempty
    }

-- | Resolve user-supplied axioms in terms of Template Haskell names to their
-- internal Core representation.
--
-- Check 'PluginAxiom' for a more detailed explanation of user axioms.
--
-- In short, this function will resolve the Template Haskell names to their
-- respective TyCon, Id or CoreExpr. Afterwards, it will supply any 'Coercible'
-- instance as provided by the type-level axioms. The modified 'CoreExpr' is
-- then checked to match exactly the type of the 'Id' that maps to it to ensure
-- correctness.
--
-- Lastly, this also ensures that mappings are only made for OPAQUE functions.
-- A special case here we do allow is a NOINLINE function without an unfolding.
-- For these, we do not use any of the user-provided coercions.
resolvePluginAxioms
  :: HasCallStack
  -- TODO: Adjust these errors!
  => Error () :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Context Reader CoreProgram :> es
  => Context Reader [TyCon] :> es
  => PluginAxioms
  -> Eff es PluginAxiomsR
resolvePluginAxioms PluginAxioms { .. } = do
  -- Get the typeclass we want to instantiate.
  embedCls <- thNameToGhcName >=> lookupClass $ ''Embeddable

  -- Resolve the type-level axioms. This is simply a lookup for the TyCon.
  typeAxiomsRList <- for (toList typeAxioms) \(orig, interp) -> do
    let resolve = thNameToGhcName >=> lookupTyConAll
    -- TODO: Should we ensure that the original TyCon is a data-type or newtype?
    -- Otherwise, the conversion might be very fragile!
    orig' <- resolve orig
    interp' <- resolve interp
    pure (orig', interp')

  -- Gather the dictionary map for instance resolution.
  dicts <- foldM' emptyTM typeAxiomsRList \dicts (tcR, tcL) -> do
    -- Gather the information to construct the coercion.
    let prov = PluginProv "pantomime user-defined"
    let tyL = mkTyConTy tcL
    let tyR = mkTyConTy tcR
    let co = mkUnivCo prov Representational tyL tyR

    let typeRepr ty = failWith () do
          (sort, rty) <- sORTKind_maybe $ typeKind ty
          case sort of
            TypeLike -> pure rty
            ConstraintLike -> empty

    -- Gather the information to construct the final dictionary.
    repL <- typeRepr tyL
    repR <- typeRepr tyR
    let con = Var . dataConWorkId . classDataCon $ embedCls
    -- TODO: For now, we're not really constructing the private typeclass
    -- correctly. I don't think it's important for our use case, but it is not
    -- very nice to do it like this.
    let private = unitExpr

    -- Construct the embed function.
    let (idE, _) = freshId "arg" (unrestricted tyL) emptyInScopeSet
    let embed = Lam idE $ mkCast (Var idE) co

    -- Construct the project function.
    let (idP, _) = freshId "arg" (unrestricted tyR) emptyInScopeSet
    let project = Lam idP $ mkCast (Var idP) (mkSymCo co)

    -- Construct the typeclass dictionary.
    let dict = mkApps con
          [ Type repL
          , Type repR
          , Type tyL
          , Type tyR
          , private
          , embed
          , project
          ]
    let ty = exprType dict
    pure $ insertTM ty dict dicts

  -- TODO: We should first ensure that termAxioms do not contain duplicate
  -- definitions.

  -- Gather a binder mapping for a substitution. This will use the dictionary
  -- map to supply coercions to any Opaque values that require it.
  termAxiomsR <- for termAxioms \(orig, interp) -> do
    -- Resolve the names as identifiers.
    let resolve = thNameToGhcName >=> lookupIdAll
    orig' <- resolve orig
    interp' <- resolve interp

    -- Gather the expression of the interpretation.
    -- TODO: Should we also attempt to get it from the local bindings?
    expr <- case realIdUnfolding interp' of
      CoreUnfolding { uf_tmpl } -> pure uf_tmpl
      _ -> throwError_ ()

    -- Check whether the original target can be interpreted.
    expr' <- case inl_inline $ idInlinePragma orig' of
      -- Opaque values can be fully interpreted. Hence, we resolve any coercions
      -- that were provided by the user.
      Opaque _ -> pure $ resolveInstancesWith dicts expr

      -- We only want to interpret no-inline if the unfolding was not available.
      NoInline _ | not . hasCoreUnfolding $ realIdUnfolding orig' -> pure expr

      -- It is fragile to interpret inlineable instances, as they may already
      -- have been optimised away.
      -- FIXME: It seems that the 'noinline' function has a NOINLINE pragma
      -- but when testing it here, it doesn't. I feel like this test is the
      -- correct one but it doesn't work in this case. I'll leave it like this
      -- for now.
      --
      -- Actually, I ran into an issue where the function I wanted to call had
      -- a NOINLINE on an inner value (that was not exported). Perhaps it still
      -- makes sense to overwrite definitions, even if they can be inlined? I
      -- guess it is still pretty fragile...
      -- _ -> throwError_ ()
      _ -> pure expr

    -- Check whether the interpretation matches.
    -- TODO: We should allow types that require less dictionaries. The CoreExpr
    -- should be adjusted to have them as arguments, but leave them unused.
    -- Very likely, we can use the unification code we already have. We just
    -- want to see after unifying and applying all dictionaries from both of
    -- them, that the type is actually the same as the original. This also
    -- immediately shapes the expression into the correct form!
    unless (varType orig' `eqType` exprType expr') do
      throwError_ ()

    -- Return the mapping.
    pure (orig', expr')

  -- Collect the resolved type and term mappings.
  pure PluginAxiomsR
    { typeAxiomsR = mkTyConEnv typeAxiomsRList
    , termAxiomsR
    }
