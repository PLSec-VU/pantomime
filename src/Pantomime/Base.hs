{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Pantomime.Base
  ( baseValues
  , integerToInt'#
  ) where

import GHC.Plugins hiding (thNameToGhcName)
import GHC.Types.TyThing (lookupId)
import GHC.Base (noinline)

import GHC.Real (overflowError, divZeroError)
import GHC.Num.Integer (integerToInt#, integerToWord#)
import GHC.Num.Natural (naturalToWord#)

import Control.Monad.Except (MonadError(..))

import Grisette hiding (Fresh)

import Pantomime.Value
import Pantomime.MonadEval
import Pantomime.WordSize
import Pantomime.Runtime

import Language.Haskell.TH qualified as TH

import Effectful
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.GHC.External
import Effectful.Error.Static (Error, throwError_)
import Effectful.Grisette.Fresh

baseValues
  :: forall es ws
   . Error EvalError :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasFamInstEnvs :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Fresh :> es
  => KnownWordSize ws
  => Eff es [(Var, Value (Eff es) ws)]
baseValues = sequence
  [ integerToInt'#
  , integerToWord'#
  -- , integerShiftL'#
  , naturalToWord'#
  -- , integerToNatural'
  -- , integerMod'
  , overflowError'
  , divZeroError'
  , interpNoInline
  ]

integerToInt'#
  :: forall es ws
   . Error EvalError :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
integerToInt'# = do
  name <- thNameToGhcName 'integerToInt#
  var <- lookupId name

  let value = Fun integerTy $ \case
        Data adt -> do
          let condIS = adtIsDataCon adt integerISDataCon
          valueIS <- case adtDataConFields adt integerISDataCon of
            Just [Primitive (Int i)] -> pure i
            _ -> throwError_ IllTyped

          let condIP = adtIsDataCon adt integerIPDataCon
          valueIP <- case adtDataConFields adt integerIPDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
            _ -> throwError_ IllTyped

          let condIN = adtIsDataCon adt integerINDataCon
          valueIN <- case adtDataConFields adt integerINDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ negate . symFromIntegral <$> i
            _ -> throwError_ IllTyped

          let alts =
                [ (condIS, valueIS)
                , (condIP, valueIP)
                , (condIN, valueIN)
                ]

          let invalid = throwError Invalid

          let foldl'' acc xs f = foldl' f acc xs

          -- FIXME: This unfolds the prerequisites for the tag multiple times,
          -- potentially bloating the guard.
          let final = foldl'' invalid alts \fl (cond, body) -> do
                cond' <- cond
                mrgIte cond' body fl

          pure . Primitive . Int $ final

        _ -> throwError_ IllTyped

  pure (var, value)

integerToWord'#
  :: forall es ws
   . Error EvalError :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
integerToWord'# = do
  name <- thNameToGhcName 'integerToWord#
  var <- lookupId name

  let value = Fun integerTy $ \case
        Data adt -> do
          let condIS = adtIsDataCon adt integerISDataCon
          valueIS <- case adtDataConFields adt integerISDataCon of
            Just [Primitive (Int i)] -> pure $ toUnsigned <$> i
            _ -> throwError_ IllTyped

          let condIP = adtIsDataCon adt integerIPDataCon
          valueIP <- case adtDataConFields adt integerIPDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
            _ -> throwError_ IllTyped

          let condIN = adtIsDataCon adt integerINDataCon
          valueIN <- case adtDataConFields adt integerINDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ negate . symFromIntegral <$> i
            _ -> throwError_ IllTyped

          let alts =
                [ (condIS, valueIS)
                , (condIP, valueIP)
                , (condIN, valueIN)
                ]

          let invalid = throwError Invalid

          let foldl'' acc xs f = foldl' f acc xs

          -- FIXME: This unfolds the prerequisites for the tag multiple times,
          -- potentially bloating the guard.
          let final = foldl'' invalid alts $ \fl (cond, body) -> do
                cond' <- cond
                mrgIte cond' body fl

          pure . Primitive . Word $ final

        _ -> throwError_ IllTyped

  pure (var, value)

naturalToWord'#
  :: forall es ws
   . Error EvalError :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
naturalToWord'# = do
  name <- thNameToGhcName 'naturalToWord#
  var <- lookupId name

  let value = Fun naturalTy $ \case
        Data adt -> do
          let condNS = adtIsDataCon adt naturalNSDataCon
          valueNS <- case adtDataConFields adt naturalNSDataCon of
            Just [Primitive (Word w)] -> pure w
            _ -> throwError_ IllTyped

          let condNB = adtIsDataCon adt naturalNBDataCon
          valueNB <- case adtDataConFields adt naturalNBDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
            _ -> throwError_ IllTyped

          let alts =
                [ (condNS, valueNS)
                , (condNB, valueNB)
                ]

          let invalid = throwError Invalid

          let foldl'' acc xs f = foldl' f acc xs

          -- FIXME: This unfolds the prerequisites for the tag multiple times,
          -- potentially bloating the guard.
          let final = foldl'' invalid alts $ \fl (cond, body) -> do
                cond' <- cond
                mrgIte cond' body fl

          pure . Primitive . Word $ final

        _ -> throwError_ IllTyped

  pure (var, value)

-- integerShiftL'#
--   :: forall m m' ws
--    . MonadCore m
--   => MonadFail m
--   => MonadEval m'
--   => KnownWordSize ws
--   => m (Var, Value m' ws)
-- integerShiftL'# = do
--   name <- thNameToGhcName' 'integerShiftL#
--     ??= "Lookup failed."
--   var <- liftCore $ lookupId name

--   let value = Fun integerTy $ \case
--         Data adt -> pure . Fun wordPrimTy $ \case
--           Primitive (Word w) -> do
--             dbg adt
--             dbg' $ show w
--             dbg' "rigged!"
--             pure $ Data adt
--             -- undefined
--             -- let condIS = adtIsDataCon adt integerISDataCon
--             -- valueIS <- case adtDataConFields adt integerISDataCon of
--             --   Just [Primitive (Int i)] -> pure i
--             --   _ -> throwError IllTyped

--             -- let condIP = adtIsDataCon adt integerIPDataCon
--             -- valueIP <- case adtDataConFields adt integerIPDataCon of
--             --   Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
--             --   _ -> throwError IllTyped

--             -- let condIN = adtIsDataCon adt integerINDataCon
--             -- valueIN <- case adtDataConFields adt integerINDataCon of
--             --   Just [Primitive (ByteArray _ i)] -> pure $ negate . symFromIntegral <$> i
--             --   _ -> throwError IllTyped

--             -- let alts =
--             --       [ (condIS, valueIS)
--             --       , (condIP, valueIP)
--             --       , (condIN, valueIN)
--             --       ]

--             -- let invalid = throwError Invalid

--             -- let foldl'' acc xs f = foldl' f acc xs

--             -- -- FIXME: This unfolds the prerequisites for the tag multiple times,
--             -- -- potentially bloating the guard.
--             -- let final = foldl'' invalid alts $ \fl (cond, body) -> do
--             --       cond' <- cond
--             --       mrgIte cond' body fl

--             -- pure $ Data adt
--             --   { adtTag = undefined
--             --   , adtFields = undefined
--             --   }
--           _ -> throwError IllTyped

--         _ -> throwError IllTyped

--   pure (var, value)

-- integerToNatural'
--   :: forall m m' ws
--    . MonadCore m
--   => MonadFail m
--   => MonadEval m'
--   => KnownWordSize ws
--   => m (Var, Value m' ws)
-- integerToNatural' = do
--   name <- thNameToGhcName' 'integerToNatural
--     ??= "Lookup failed."
--   var <- liftCore $ lookupId name

--   let value = Fun integerTy $ \case
--         Data adt -> do
--           dbg adt
--           dbg' "rigged!"
--           -- FIXME: This rig isn't even typed correctly... Or more presisely,
--           -- it's fields are just bad.
--           pure $ Data adt
--             { adtTyCon = naturalTyCon
--             , adtTyArgs = []
--             , adtTag = pure 0
--             , adtFields = [[Primitive . Word . pure $ 0], [Data ADT {}]]
--             }
--         _ -> throwError IllTyped

--   pure (var, value)

-- integerMod'
--   :: forall m m' ws
--    . MonadCore m
--   => MonadFail m
--   => MonadEval m'
--   => KnownWordSize ws
--   => m (Var, Value m' ws)
-- integerMod' = do
--   name <- thNameToGhcName' 'integerMod
--     ??= "Lookup failed."
--   var <- liftCore $ lookupId name

--   let value = Fun integerTy $ \case
--         Data lhs -> pure . Fun integerTy $ \case
--           Data rhs -> do
--             dbg lhs
--             dbg rhs
--             dbg' "rigged!"
--             pure $ Data lhs
--           _ -> throwError IllTyped
--         _ -> throwError IllTyped

--   pure (var, value)

overflowError'
  :: forall es ws
   . Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error EvalError :> es
  => Fresh :> es
  => HasThings :> es
  => HasFamInstEnvs :> es
  => THNameToGHCName :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
overflowError' = do
  name <- thNameToGhcName 'overflowError
  var <- lookupId name

  let value = Fun tYPEKind $ \case
        Ty ty -> evalFresh (ty, Left @_ @() Overflow)
        _ -> throwError_ IllTyped

  pure (var, value)

divZeroError'
  :: forall es ws
   . Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error EvalError :> es
  => Fresh :> es
  => HasThings :> es
  => HasFamInstEnvs :> es
  => THNameToGHCName :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
divZeroError' = do
  name <- thNameToGhcName 'divZeroError
  var <- lookupId name

  let value = Fun tYPEKind $ \case
        Ty ty -> evalFresh (ty, Left @_ @() DivideByZero)
        _ -> throwError_ IllTyped

  pure (var, value)

interpNoInline
  :: forall es ws
   . Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error EvalError :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Eff es (Var, Value (Eff es) ws)
interpNoInline = do
  name <- thNameToGhcName 'noinline
  var <- lookupId name
  let value = Fun tYPEKind $ \case
        Ty ty -> pure . Fun ty $ \arg -> pure arg
        _ -> throwError_ IllTyped
  pure (var, value)
