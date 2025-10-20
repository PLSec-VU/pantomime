{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Axiom
  ( PluginAxioms (..)
  , PluginAxiomsR (..)
  , resolvePluginAxioms
  ) where

import Language.Haskell.TH qualified as TH

import GHC.Core.TyCo.Rep (UnivCoProvenance(..))
import GHC.Core.TyCon.Env (TyConEnv, mkTyConEnv)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Data.TrieMap (insertTM, TrieMap (..))
import GHC.Plugins
  ( Unfolding (..)
  , InlineSpec (..)
  , TyCon (..)
  , Name
  , CoreExpr
  , CoreProgram
  , IdEnv
  , Role (..)
  , Expr (..)
  , Var (..)
  , InlinePragma (..)
  , mkTyConApp
  , mkUnivCo
  , dataConWorkId
  , coercibleDataCon
  , mkApps
  , exprType
  , hasCoreUnfolding
  , idUnfolding
  , idInlinePragma
  , mkVarEnv
  )

import GHC.Exts (IsList(..))

import Control.Monad ((>=>), unless)

import Data.Data (Data)
import Data.Function (on)
import Data.Map (Map)
import Data.Typeable (Typeable)
import Data.Traversable (for)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.Context

import Pantomime.Unification (resolveInstancesWith)
import Pantomime.Util (foldM')
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsDoc (..)
  , hang
  )

-- | User axioms only visible to the plugin.
--
-- The kinds and types of the mapped terms should match up exactly. The
-- exception is that type-level axioms will be used to instantiate requirements
-- of 'Coercible' on any term-level axiom.
--
-- # Example
--
-- Suppose the user has some bitvector type called 'Signed'.
--
-- > type Signed (n :: Nat) = ...
--
-- The user supplies the following mapping:
--
-- > Signed |-> IntN
--
-- This roughly says that the user wants to use the underlying bitvector
-- representation IntN. IntN is treated as a primitive within the plugin and is
-- implemented using the respective SMT theory. A mapping between non-primitive
-- types is also allowed (or any mixing of these, use type aliases for this).
--
-- Now, a user has some functions that operate on 'Signed'. These of course
-- require a mapping to the their respective operation on 'IntN'. Before
-- anything, a user needs to ensure that **ALL** operations on 'Signed' are
-- through functions marked as 'OPAQUE' and that it's constructor is not
-- exported. This is to ensure correctness within the evaluator, as otherwise
-- representational equivalence is broken.
--
-- With this in mind, the following will illustrate how to write an
-- interpretation. Suppose we have an addition function for 'Signed' values.
--
-- > {-# OPAQUE plusSigned #-}
-- > plusSigned :: KnownNat n => Signed n -> Signed n -> Signed n
--
-- We can write an interpretation for this using the addition as provided by
-- 'IntN'. The importance lies in using a coercion 'Coercible Signed IntN'.
--
-- > plusInterp
-- >   :: Coercible Signed IntN
-- >   => KnownNat n
-- >   => Signed n
-- >   -> Signed n
-- >   -> Signed n
-- > plusInterp = go
-- >   where
-- >     go :: bv ~ IntN => bv n -> bv n -> bv n
-- >     go = coerce plusIntN
--
-- Note, the where clause is only to trick Haskell into allowing the coercion
-- to appear at the top level. With this defintion in place, we supply the
-- appropriate mapping:
--
-- > plusSigned |-> plusInterp
--
-- Of course, the types for 'plusSigned' and 'plusInterp' do not match up
-- one-to-one. That is, to complete the interpretation, we supply 'plusInterp'
-- with the user-supplied coercion that 'Coercible Signed IntN'. Afterwards, the
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
    , termAxioms :: Map TH.Name TH.Name
    -- ^ Term-level representational equivalence axioms.
    --
    -- Both the key and value of these mappings should be resolvable to 'Id'.
    -- This can be used to operate on types that have user-provided equivalence
    -- axioms via 'typeAxioms'. The types should match exactly between both
    -- 'Id's, with the exception of 'Coercible' instances that may be resolved
    -- using the 'typeAxioms'.
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

-- | Fully resolved plugin axioms. These may be used as-is by the solver.
data PluginAxiomsR where
  PluginAxiomsR ::
    { typeAxiomsR :: TyConEnv TyCon
    -- ^ Type-level axioms, mainly used to construct symbolic values.
    , termAxiomsR :: IdEnv CoreExpr
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
  => PluginAxioms
  -> Eff es PluginAxiomsR
resolvePluginAxioms PluginAxioms { .. } = do
  -- Resolve the type-level axioms. This is simply a lookup for the TyCon.
  typeAxiomsRList <- for (toList typeAxioms) \(orig, interp) -> do
    -- TODO: Add lookup for local TyCon declarations.
    let resolve = thNameToGhcName >=> lookupTyCon
    -- TODO: Should we ensure that the original TyCon is a data-type or newtype?
    -- Otherwise, the conversion might be very fragile!
    orig' <- resolve orig
    interp' <- resolve interp
    pure (orig', interp')

  -- Creates a boxed coercion between the given TyCon.
  let mkPluginTcCo tcL tcR = do
        -- Get the kind of the coercible TyCon.
        let kind = tyConKind tcL

        -- Ensure the kind and roles match up.
        let eqKinds = eqType kind $ tyConKind tcR
        let eqRoles = all (uncurry (==)) $ on zip tyConRoles tcL tcR
        unless (eqKinds && eqRoles) do
          throwError_ ()

        -- Gather the remaining information to construct the coercion.
        let prov = PluginProv "pantomime user-defined"
        let tyL = mkTyConApp tcL []
        let tyR = mkTyConApp tcR []
        let co = mkUnivCo prov Representational tyL tyR

        -- Box the coercion.
        let eqVar = Var $ dataConWorkId coercibleDataCon
        pure $ mkApps eqVar [Type kind, Type tyL, Type tyR, Coercion co]

  -- Inserts a coercion between two TyCon into the given dictionary.
  let insertCo tcL tcR dicts = do
        dict <- mkPluginTcCo tcL tcR
        let ty = exprType dict
        pure $ insertTM ty dict dicts

  -- Gather the dictionary map for instance resolution.
  dicts <- foldM' emptyTM typeAxiomsRList \dicts (orig, interp) -> do
    -- Add both directions of the coercion to the dictionary map.
    insertCo orig interp >=> insertCo interp orig $ dicts

  -- Gather a binder mapping for a substitution. This will use the dictionary
  -- map to supply coercions to any Opaque values that require it.
  termAxiomsRList <- for (toList termAxioms) \(orig, interp) -> do
    -- Resolve the names as identifiers.
    let resolve = thNameToGhcName >=> lookupIdAll
    orig' <- resolve orig
    interp' <- resolve interp

    -- Gather the expression of the interpretation.
    -- TODO: Should we also attempt to get it from the local bindings?
    expr <- case idUnfolding interp' of
      CoreUnfolding { uf_tmpl } -> pure uf_tmpl
      _ -> throwError_ ()

    -- Check whether the original target can be interpreted.
    expr' <- case inl_inline $ idInlinePragma orig' of
      -- Opaque values can be fully interpreted. Hence, we resolve any coercions
      -- that were provided by the user.
      Opaque _ -> pure $ resolveInstancesWith dicts expr

      -- We only want to interpret no-inline if the unfolding was not available.
      NoInline _ | hasCoreUnfolding $ idUnfolding orig' -> pure expr

      -- It is fragile to interpret inlineable instances, as they may already
      -- have been optimised away.
      _ -> throwError_ ()

    -- Check whether the interpretation matches.
    unless (varType orig' `eqType` exprType expr') do
      throwError_ ()

    -- Return the mapping.
    pure (orig', expr')

  -- Collect the resolved type and term mappings.
  pure PluginAxiomsR
    { typeAxiomsR = mkTyConEnv typeAxiomsRList
    , termAxiomsR = mkVarEnv termAxiomsRList
    }
