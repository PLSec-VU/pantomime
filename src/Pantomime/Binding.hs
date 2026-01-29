module Pantomime.Binding
  ( getBuiltinTyCon
  , bindingsGHC
  ) where


import Control.Error (LookupError)
import Data.Traversable (for)
import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.External (HasFamInstEnvs)
import Effectful.GHC.TyThing (HasThings, lookupTyCon, lookupId)
import Effectful.GHC.TH (THNameToGHCName, thNameToGhcName)
import GHC.Plugins (Name, TyCon, Var)
import GHC.TypeNats qualified as Builtin (KnownNat, type (<=))
import Language.Haskell.TH qualified as TH
import Pantomime.BuiltIn qualified as Builtin
import Pantomime.PrimOps qualified as PrimOps
import Pantomime.Literal (BuiltInTyCon (..))
import Pantomime.Expr (EvalExpr)


-- TODO: I need a better name for this!
-- data Binds where
--   Binds ::
--     { toIntId :: Id
--     , toInt8Id :: Id
--     , toInt16Id :: Id
--     , toInt32Id :: Id
--     , toInt64Id :: Id
--     } -> Binds

thNameToTyCon
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => TH.Name
  -> Eff es TyCon
thNameToTyCon th = do
  name <- thNameToGhcName th
  lookupTyCon name

getBuiltinTyCon
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Eff es BuiltInTyCon
getBuiltinTyCon = do
  tcBool <- thNameToTyCon ''Builtin.Bool
  tcBitVec <- thNameToTyCon ''Builtin.BitVec
  tcInteger <- thNameToTyCon ''Builtin.Integer
  tcArray <- thNameToTyCon ''Builtin.Array
  tcPrimitive <- thNameToTyCon ''Builtin.Primitive
  tcKnownNat <- thNameToTyCon ''Builtin.KnownNat
  tcLEqNat <- thNameToTyCon ''(Builtin.<=)
  pure BuiltInTyCon { .. }

bindingsTH
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => [(TH.Name, EvalExpr es)]
bindingsTH =
  -- System Fc bindings
  [ ('Builtin.ite, PrimOps.ite)
  , ('Builtin.tagToEnum, PrimOps.tagToEnum)
  , ('Builtin.dataToTag, PrimOps.dataToTag)

  -- Boolean bindings
  , ('Builtin.true, PrimOps.true)
  , ('Builtin.false, PrimOps.false)
  , ('Builtin.not, PrimOps.not)
  , ('(Builtin.&&), PrimOps.and)
  , ('(Builtin.||), PrimOps.or)
  , ('Builtin.implies, PrimOps.implies)
  , ('Builtin.xor, PrimOps.xor)
  , ('Builtin.iff, PrimOps.iff)

  -- Integer bindings
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

  -- Bitvector bindings
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
  , ('Builtin.bvselect, PrimOps.bvselect)

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
