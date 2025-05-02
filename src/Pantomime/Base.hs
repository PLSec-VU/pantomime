{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Pantomime.Base
  ( baseValues
  , integerToInt'#
  ) where

import GHC.Plugins
import GHC.Types.TyThing (lookupId)
import GHC.Base (noinline)

import GHC.Real (overflowError, divZeroError)
import GHC.Num.Integer (integerToInt#, integerToWord#)
import GHC.Num.Natural (naturalToWord#)

import Control.Monad.Except (MonadError(..))

import Grisette

import Util

import Pantomime.Value
import Pantomime.MonadEval
import Pantomime.WordSize
import Pantomime.Runtime
import Pantomime.Clash.Util
import Pantomime.Monad.GHC

baseValues
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m [(Var, Value m ws)]
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
  :: forall m m' ws
   . MonadCore m
  => MonadFail m
  => MonadEval m'
  => KnownWordSize ws
  => m (Var, Value m' ws)
integerToInt'# = do
  name <- thNameToGhcName' 'integerToInt#
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  let value = Fun integerTy $ \case
        Data adt -> do
          let condIS = adtIsDataCon adt integerISDataCon
          valueIS <- case adtDataConFields adt integerISDataCon of
            Just [Primitive (Int i)] -> pure i
            _ -> throwError IllTyped

          let condIP = adtIsDataCon adt integerIPDataCon
          valueIP <- case adtDataConFields adt integerIPDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
            _ -> throwError IllTyped

          let condIN = adtIsDataCon adt integerINDataCon
          valueIN <- case adtDataConFields adt integerINDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ negate . symFromIntegral <$> i
            _ -> throwError IllTyped

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

          pure . Primitive . Int $ final

        _ -> throwError IllTyped

  pure (var, value)

integerToWord'#
  :: forall m m' ws
   . MonadCore m
  => MonadFail m
  => MonadEval m'
  => KnownWordSize ws
  => m (Var, Value m' ws)
integerToWord'# = do
  name <- thNameToGhcName' 'integerToWord#
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  let value = Fun integerTy $ \case
        Data adt -> do
          let condIS = adtIsDataCon adt integerISDataCon
          valueIS <- case adtDataConFields adt integerISDataCon of
            Just [Primitive (Int i)] -> pure $ toUnsigned <$> i
            _ -> throwError IllTyped

          let condIP = adtIsDataCon adt integerIPDataCon
          valueIP <- case adtDataConFields adt integerIPDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
            _ -> throwError IllTyped

          let condIN = adtIsDataCon adt integerINDataCon
          valueIN <- case adtDataConFields adt integerINDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ negate . symFromIntegral <$> i
            _ -> throwError IllTyped

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

        _ -> throwError IllTyped

  pure (var, value)

naturalToWord'#
  :: forall m m' ws
   . MonadCore m
  => MonadFail m
  => MonadEval m'
  => KnownWordSize ws
  => m (Var, Value m' ws)
naturalToWord'# = do
  name <- thNameToGhcName' 'naturalToWord#
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  let value = Fun naturalTy $ \case
        Data adt -> do
          let condNS = adtIsDataCon adt naturalNSDataCon
          valueNS <- case adtDataConFields adt naturalNSDataCon of
            Just [Primitive (Word w)] -> pure w
            _ -> throwError IllTyped

          let condNB = adtIsDataCon adt naturalNBDataCon
          valueNB <- case adtDataConFields adt naturalNBDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
            _ -> throwError IllTyped

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

        _ -> throwError IllTyped

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
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
overflowError' = do
  name <- thNameToGhcName' 'overflowError
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  let value = Fun tYPEKind $ \case
        Ty ty -> typedValue (throwError Overflow) ty
        _ -> throwError IllTyped

  pure (var, value)

divZeroError'
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
divZeroError' = do
  name <- thNameToGhcName' 'divZeroError
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  let value = Fun tYPEKind $ \case
        Ty ty -> typedValue (throwError DivideByZero) ty
        _ -> throwError IllTyped

  pure (var, value)

interpNoInline
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpNoInline = do
  var <- lookupThId 'noinline
  let value = Fun tYPEKind $ \case
        Ty ty -> pure . Fun ty $ \arg -> pure arg
        _ -> throwError IllTyped
  pure (var, value)
