{-# LANGUAGE MagicHash #-}
module Pantomime.Binding
  ( InterfaceThings (..)
  , getInterfaceThings
  , getBuiltinTyCon
  , bindingsGHC
  ) where


import Control.Error (LookupError)
import Control.Monad ((>=>))
import Data.Traversable (for)
import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.External (HasFamInstEnvs)
import Effectful.GHC.TyThing (HasThings, lookupTyCon, lookupId)
import Effectful.GHC.TH (THNameToGHCName, thNameToGhcName)
import GHC.Plugins (Name, Var, Id)
import GHC.TypeNats qualified as Builtin (KnownNat, type (<=))
import Language.Haskell.TH qualified as TH
import Pantomime.BuiltIn qualified as Builtin
import Pantomime.PrimOps qualified as PrimOps
import Pantomime.Literal (BuiltInTyCon (..))
import Pantomime.Expr (EvalExpr)
import Unsafe.Coerce qualified as Builtin (UnsafeEquality, unsafeEqualityProof)

-- TODO: I need a better name for this!
-- I guess these could also be 'BuiltInOps', 'BuiltInIds' or at least something
-- to signify what these are used for?
data InterfaceThings where
  InterfaceThings ::
    { toIntId :: Id
    , toInt8Id :: Id
    , toInt16Id :: Id
    , toInt32Id :: Id
    , toInt64Id :: Id
    , toWordId :: Id
    , toWord8Id :: Id
    , toWord16Id :: Id
    , toWord32Id :: Id
    , toWord64Id :: Id
    , eqIntId :: Id
    , eqInt8Id :: Id
    , eqInt16Id :: Id
    , eqInt32Id :: Id
    , eqInt64Id :: Id
    , eqWordId :: Id
    , eqWord8Id :: Id
    , eqWord16Id :: Id
    , eqWord32Id :: Id
    , eqWord64Id :: Id
    } -> InterfaceThings

getInterfaceThings
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Eff es InterfaceThings
getInterfaceThings = do
  let thNameToId = thNameToGhcName >=> lookupId
  toIntId <- thNameToId 'Builtin.toInt#
  toInt8Id <- thNameToId 'Builtin.toInt8#
  toInt16Id <- thNameToId 'Builtin.toInt16#
  toInt32Id <- thNameToId 'Builtin.toInt32#
  toInt64Id <- thNameToId 'Builtin.toInt64#
  toWordId <- thNameToId 'Builtin.toWord#
  toWord8Id <- thNameToId 'Builtin.toWord8#
  toWord16Id <- thNameToId 'Builtin.toWord16#
  toWord32Id <- thNameToId 'Builtin.toWord32#
  toWord64Id <- thNameToId 'Builtin.toWord64#
  eqIntId <- thNameToId 'Builtin.eqInt#
  eqInt8Id <- thNameToId 'Builtin.eqInt8#
  eqInt16Id <- thNameToId 'Builtin.eqInt16#
  eqInt32Id <- thNameToId 'Builtin.eqInt32#
  eqInt64Id <- thNameToId 'Builtin.eqInt64#
  eqWordId <- thNameToId 'Builtin.eqWord#
  eqWord8Id <- thNameToId 'Builtin.eqWord8#
  eqWord16Id <- thNameToId 'Builtin.eqWord16#
  eqWord32Id <- thNameToId 'Builtin.eqWord32#
  eqWord64Id <- thNameToId 'Builtin.eqWord64#
  pure InterfaceThings { .. }

getBuiltinTyCon
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Eff es BuiltInTyCon
getBuiltinTyCon = do
  let thNameToTyCon = thNameToGhcName >=> lookupTyCon
  tcBool <- thNameToTyCon ''Builtin.Bool
  tcBitVec <- thNameToTyCon ''Builtin.BitVec
  tcInteger <- thNameToTyCon ''Builtin.Integer
  tcArray <- thNameToTyCon ''Builtin.Array
  tcPrimitive <- thNameToTyCon ''Builtin.Primitive
  tcKnownNat <- thNameToTyCon ''Builtin.KnownNat
  tcLEqNat <- thNameToTyCon ''(Builtin.<=)
  tcUnsafeEquality <- thNameToTyCon ''Builtin.UnsafeEquality
  pure BuiltInTyCon { .. }

bindingsTH
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => [(TH.Name, EvalExpr es)]
bindingsTH =
  -- System FC bindings.
  ----------------------
  [ ('Builtin.ite, PrimOps.ite)
  , ('Builtin.tagToEnum, PrimOps.tagToEnum)
  , ('Builtin.dataToTag, PrimOps.dataToTag)
  , ('Builtin.raise, PrimOps.raise)
  , ('Builtin.unsafeEqualityProof, PrimOps.unsafeEqualityProof)

  -- Boolean bindings.
  --------------------
  , ('Builtin.true, PrimOps.true)
  , ('Builtin.false, PrimOps.false)
  , ('Builtin.not, PrimOps.not)
  , ('(Builtin.&&), PrimOps.and)
  , ('(Builtin.||), PrimOps.or)
  , ('Builtin.implies, PrimOps.implies)
  , ('Builtin.xor, PrimOps.xor)
  , ('Builtin.iff, PrimOps.iff)

  -- Integer bindings.
  --------------------
  , ('Builtin.i2bv, PrimOps.i2bv)
  , ('Builtin.ineg, PrimOps.ineg)
  , ('Builtin.iabs, PrimOps.iabs)
  , ('Builtin.iadd, PrimOps.iadd)
  , ('Builtin.imul, PrimOps.imul)
  , ('Builtin.idiv, PrimOps.idiv)
  , ('Builtin.imod, PrimOps.imod)
  , ('Builtin.ieq, PrimOps.ieq)
  , ('Builtin.ineq, PrimOps.ineq)
  , ('Builtin.ile, PrimOps.ile)
  , ('Builtin.ilt, PrimOps.ilt)

  -- Bitvector bindings.
  ----------------------
  , ('Builtin.bv2i, PrimOps.bv2i)
  , ('Builtin.bvsize, PrimOps.bvsize)
  , ('Builtin.bvnot, PrimOps.bvnot)
  , ('Builtin.bvneg, PrimOps.bvneg)
  , ('Builtin.bvand, PrimOps.bvand)
  , ('Builtin.bvor, PrimOps.bvor)
  , ('Builtin.bvxor, PrimOps.bvxor)
  , ('Builtin.bvadd, PrimOps.bvadd)
  , ('Builtin.bvmul, PrimOps.bvmul)
  , ('Builtin.bvudiv, PrimOps.bvudiv)
  , ('Builtin.bvsdiv, PrimOps.bvsdiv)
  , ('Builtin.bvurem, PrimOps.bvurem)
  , ('Builtin.bvsrem, PrimOps.bvsrem)
  , ('Builtin.bvshl, PrimOps.bvshl)
  , ('Builtin.bvlshr, PrimOps.bvlshr)
  , ('Builtin.bvashr, PrimOps.bvashr)
  , ('Builtin.bveq, PrimOps.bveq)
  , ('Builtin.bvneq, PrimOps.bvneq)
  , ('Builtin.bvule, PrimOps.bvule)
  , ('Builtin.bvsle, PrimOps.bvsle)
  , ('Builtin.bvult, PrimOps.bvult)
  , ('Builtin.bvslt, PrimOps.bvslt)
  , ('Builtin.bvconcat, PrimOps.bvconcat)
  , ('Builtin.bvzext, PrimOps.bvzext)
  , ('Builtin.bvsext, PrimOps.bvsext)
  , ('Builtin.bvselect, PrimOps.bvselect)

  -- Array bindings.
  ------------------
  , ('Builtin.aconst, PrimOps.aconst)
  , ('Builtin.aselect, PrimOps.aselect)
  , ('Builtin.astore, PrimOps.astore)
  ]

bindingsGHC
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Error () :> fs
  => Context Reader BuiltInTyCon :> fs
  => HasFamInstEnvs :> fs
  => Eff es [(Var, EvalExpr fs)]
bindingsGHC = for bindingsTH \(th, expr) -> do
  name <- thNameToGhcName th
  var <- lookupId name
  pure (var, expr)
