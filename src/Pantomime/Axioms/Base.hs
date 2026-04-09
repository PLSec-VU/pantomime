{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UnboxedTuples #-}
-- NOTE: We really want 'Pantomime' to be able to find these variables!
{-# OPTIONS_GHC "-fexpose-all-unfoldings" #-}

module Pantomime.Axioms.Base
  ( axioms
  ) where

import Control.Exception.Base qualified as GHC (patError)
import Data.Constraint.Unsafe (unsafeSNat)
import GHC.Base
  ( TYPE
  , Int#
  , Int8#
  , Int16#
  , Int32#
  , Int64#
  , Word#
  , Word8#
  , Word16#
  , Word32#
  , Word64#
  , Addr#
  , RuntimeRep (..)
  , Int (..)
  )
import GHC.Base qualified as GHC
import GHC.Exts (IsList (..))
import GHC.Num (Integer(..), Natural (..))
import GHC.Num qualified as GHC
  ( integerFromNatural
  , integerFromWord#
  , integerToInt#
  , integerToWord#
  , naturalAdd
  , naturalSubThrow
  , naturalFromBigNat#
  )
import GHC.Num.BigNat qualified as GHC
  ( bigNatFromWord#
  , bigNatToWord#
  , bigNatAddWord#
  , bigNatAdd
  , bigNatFromWord2#
  , bigNatSubWordUnsafe#
  , bigNatSub
  )
import GHC.Prim qualified as GHC
import GHC.Prim.Exception qualified as GHC
import GHC.TypeLits (KnownNat, SNat, type (+))
import GHC.TypeNats qualified as GHC (withSomeSNat)
import Pantomime (PluginAxioms (..))
import Pantomime.BuiltIn qualified as Pantomime
import Prelude hiding (undefined)
import Unsafe.Coerce (unsafeCoerce)

axioms :: PluginAxioms
axioms = PluginAxioms
  { typeAxioms = fromList
    [ (''Int#, ''BitVecPW)
    , (''Int8#, ''BitVec8)
    , (''Int16#, ''BitVec16)
    , (''Int32#, ''BitVec32)
    , (''Int64#, ''BitVec64)
    , (''Word#, ''BitVecPW)
    , (''Word8#, ''BitVec8)
    , (''Word16#, ''BitVec16)
    , (''Word32#, ''BitVec32)
    , (''Word64#, ''BitVec64)
    ]
  , termAxioms =
    -- Pantomime embed operations.
    ------------------------------
    [ ('Pantomime.toInt#, 'fromBV)
    , ('Pantomime.toInt8#, 'fromBV)
    , ('Pantomime.toInt16#, 'fromBV)
    , ('Pantomime.toInt32#, 'fromBV)
    , ('Pantomime.toInt64#, 'fromBV)
    , ('Pantomime.toWord#, 'fromBV)
    , ('Pantomime.toWord8#, 'fromBV)
    , ('Pantomime.toWord16#, 'fromBV)
    , ('Pantomime.toWord32#, 'fromBV)
    , ('Pantomime.toWord64#, 'fromBV)
    , ('Pantomime.eqInt#, 'eqI)
    , ('Pantomime.eqInt8#, 'eqI8)
    , ('Pantomime.eqInt16#, 'eqI16)
    , ('Pantomime.eqInt32#, 'eqI32)
    , ('Pantomime.eqInt64#, 'eqI64)
    , ('Pantomime.eqWord#, 'eqW)
    , ('Pantomime.eqWord8#, 'eqW8)
    , ('Pantomime.eqWord16#, 'eqW16)
    , ('Pantomime.eqWord32#, 'eqW32)
    , ('Pantomime.eqWord64#, 'eqW64)

    -- Integer to pantomime primitive conversions.
    ----------------------------------------------
    , ('Pantomime.hsi2i, 'hsi2i)
    , ('Pantomime.i2hsi, 'i2hsi)

    -- System FC primitive operations.
    ----------------------------------
    , ('GHC.tagToEnum#, 'tagToEnum)
    -- TODO: While these might be deprecated for use, they are in fact required
    -- in this context... Not sure what to do if these are unexposed (but still
    -- used internally) in the future.
    , ('GHC.dataToTagSmall#, 'dataToTag)
    , ('GHC.dataToTagLarge#, 'dataToTag)
    , ('GHC.raise#, 'Pantomime.raise)

    -- Int# primitive operations.
    -----------------------------
    , ('GHC.intToInt8#, 'intToInt8#)
    , ('GHC.intToInt16#, 'intToInt16#)
    , ('GHC.intToInt32#, 'intToInt32#)
    , ('GHC.intToInt64#, 'intToInt64#)
    , ('GHC.int2Word#, 'int2Word#)
    -- , ('GHC.int2Float#, 'undefined)
    -- , ('GHC.int2Double#, 'undefined)
    , ('(GHC.+#), '(+#))
    , ('(GHC.-#), '(-#))
    , ('(GHC.*#), '(*#))
    , ('GHC.addIntC#, 'addIntC#)
    , ('GHC.subIntC#, 'subIntC#)
    -- , ('GHC.timesInt2#, 'timesInt2#)
    -- , ('GHC.mulIntMayOflo#, 'mulIntMayOflo#)
    -- , (('GHC.quotInt#, 'quotInt#))
    -- , (('GHC.remInt#, 'remInt#))
    -- , (('GHC.quotRemInt#, 'quotRemInt#))
    , ('GHC.andI#, 'andI#)
    , ('GHC.orI#, 'orI#)
    , ('GHC.xorI#, 'xorI#)
    , ('GHC.notI#, 'notI#)
    , ('GHC.negateInt#, 'negateInt#)
    -- , ('GHC.uncheckedIShiftL#, 'uncheckedIShiftL#)
    -- , ('GHC.uncheckedIShiftRA#, 'uncheckedIShiftRA#)
    -- , ('GHC.uncheckedIShiftRL#, 'uncheckedIShiftRL#)
    , ('(GHC.==#), '(==#))
    , ('(GHC./=#), '(/=#))
    , ('(GHC.>=#), '(>=#))
    , ('(GHC.>#), '(>#))
    , ('(GHC.<=#), '(<=#))
    , ('(GHC.<#), '(<#))

    -- Int8# primitive operations.
    ------------------------------
    , ('GHC.int8ToInt#, 'int8ToInt#)
    , ('GHC.int8ToWord8#, 'int8ToWord8#)
    , ('GHC.plusInt8#, 'plusInt8#)
    , ('GHC.subInt8#, 'subInt8#)
    , ('GHC.timesInt8#, 'timesInt8#)
    -- , ('GHC.quotInt8#, 'quotInt8#)
    -- , ('GHC.remInt8#, 'remInt8#)
    -- , ('GHC.quotRemInt8#, 'quotRemInt8#)
    -- , ('GHC.uncheckedShiftLInt8#, 'uncheckedShiftLInt8#)
    -- , ('GHC.uncheckedShiftRAInt8#, 'uncheckedShiftRAInt8#)
    -- , ('GHC.uncheckedShiftRLInt8#, 'uncheckedShiftRLInt8#)
    , ('GHC.negateInt8#, 'negateInt8#)
    , ('GHC.eqInt8#, 'eqInt8#)
    , ('GHC.neInt8#, 'neInt8#)
    , ('GHC.geInt8#, 'geInt8#)
    , ('GHC.gtInt8#, 'gtInt8#)
    , ('GHC.leInt8#, 'leInt8#)
    , ('GHC.ltInt8#, 'ltInt8#)

    -- Int16# primitive operations.
    ------------------------------
    , ('GHC.int16ToInt#, 'int16ToInt#)
    , ('GHC.int16ToWord16#, 'int16ToWord16#)
    , ('GHC.plusInt16#, 'plusInt16#)
    , ('GHC.subInt16#, 'subInt16#)
    , ('GHC.timesInt16#, 'timesInt16#)
    -- , ('GHC.quotInt16#, 'quotInt16#)
    -- , ('GHC.remInt16#, 'remInt16#)
    -- , ('GHC.quotRemInt16#, 'quotRemInt16#)
    -- , ('GHC.uncheckedShiftLInt16#, 'uncheckedShiftLInt16#)
    -- , ('GHC.uncheckedShiftRAInt16#, 'uncheckedShiftRAInt16#)
    -- , ('GHC.uncheckedShiftRLInt16#, 'uncheckedShiftRLInt16#)
    , ('GHC.negateInt16#, 'negateInt16#)
    , ('GHC.eqInt16#, 'eqInt16#)
    , ('GHC.neInt16#, 'neInt16#)
    , ('GHC.geInt16#, 'geInt16#)
    , ('GHC.gtInt16#, 'gtInt16#)
    , ('GHC.leInt16#, 'leInt16#)
    , ('GHC.ltInt16#, 'ltInt16#)

    -- Int32# primitive operations.
    ------------------------------
    , ('GHC.int32ToInt#, 'int32ToInt#)
    , ('GHC.int32ToWord32#, 'int32ToWord32#)
    , ('GHC.plusInt32#, 'plusInt32#)
    , ('GHC.subInt32#, 'subInt32#)
    , ('GHC.timesInt32#, 'timesInt32#)
    -- , ('GHC.quotInt32#, 'quotInt32#)
    -- , ('GHC.remInt32#, 'remInt32#)
    -- , ('GHC.quotRemInt32#, 'quotRemInt32#)
    -- , ('GHC.uncheckedShiftLInt32#, 'uncheckedShiftLInt32#)
    -- , ('GHC.uncheckedShiftRAInt32#, 'uncheckedShiftRAInt32#)
    -- , ('GHC.uncheckedShiftRLInt32#, 'uncheckedShiftRLInt32#)
    , ('GHC.negateInt32#, 'negateInt32#)
    , ('GHC.eqInt32#, 'eqInt32#)
    , ('GHC.neInt32#, 'neInt32#)
    , ('GHC.geInt32#, 'geInt32#)
    , ('GHC.gtInt32#, 'gtInt32#)
    , ('GHC.leInt32#, 'leInt32#)
    , ('GHC.ltInt32#, 'ltInt32#)

    -- Int64# primitive operations.
    ------------------------------
    , ('GHC.int64ToInt#, 'int64ToInt#)
    , ('GHC.int64ToWord64#, 'int64ToWord64#)
    , ('GHC.plusInt64#, 'plusInt64#)
    , ('GHC.subInt64#, 'subInt64#)
    , ('GHC.timesInt64#, 'timesInt64#)
    -- , ('GHC.quotInt64#, 'quotInt64#)
    -- , ('GHC.remInt64#, 'remInt64#)
    -- , ('GHC.uncheckedIShiftL64#, 'uncheckedIShiftL64#)
    -- , ('GHC.uncheckedIShiftRA64#, 'uncheckedIShiftRA64#)
    -- , ('GHC.uncheckedIShiftRL64#, 'uncheckedIShiftRL64#)
    , ('GHC.negateInt64#, 'negateInt64#)
    , ('GHC.eqInt64#, 'eqInt64#)
    , ('GHC.neInt64#, 'neInt64#)
    , ('GHC.geInt64#, 'geInt64#)
    , ('GHC.gtInt64#, 'gtInt64#)
    , ('GHC.leInt64#, 'leInt64#)
    , ('GHC.ltInt64#, 'ltInt64#)

    -- Word# primitive operations.
    ------------------------------
    , ('GHC.wordToWord8#, 'wordToWord8#)
    , ('GHC.wordToWord16#, 'wordToWord16#)
    , ('GHC.wordToWord32#, 'wordToWord32#)
    , ('GHC.wordToWord64#, 'wordToWord64#)
    , ('GHC.word2Int#, 'word2Int#)
    -- , ('GHC.word2Float#, 'word2Float#)
    -- , ('GHC.word2Double#, 'word2Double#)
    , ('GHC.plusWord#, 'plusWord#)
    , ('GHC.minusWord#, 'minusWord#)
    , ('GHC.timesWord#, 'timesWord#)
    , ('GHC.addWordC#, 'addWordC#)
    , ('GHC.subWordC#, 'subWordC#)
    -- , ('GHC.plusWord2#, 'plusWord2#)
    -- , ('GHC.timesWord2#, 'timesWord2#)
    -- , (('GHC.quotWord#, 'quotWord#))
    -- , (('GHC.remWord#, 'remWord#))
    -- , (('GHC.quotRemWord#, 'quotRemWord#))
    -- , (('GHC.quotRemWord2#, 'quotRemWord2#))
    , ('GHC.and#, 'and#)
    , ('GHC.or#, 'or#)
    , ('GHC.xor#, 'xor#)
    , ('GHC.not#, 'not#)
    -- , ('GHC.uncheckedShiftL#, 'uncheckedShiftL#)
    , ('GHC.uncheckedShiftRL#, 'uncheckedShiftRL#)
    , ('GHC.eqWord#, 'eqWord#)
    , ('GHC.neWord#, 'neWord#)
    , ('GHC.geWord#, 'geWord#)
    , ('GHC.gtWord#, 'gtWord#)
    , ('GHC.leWord#, 'leWord#)
    , ('GHC.ltWord#, 'ltWord#)

    -- Word8# primitive operations.
    ------------------------------
    , ('GHC.word8ToWord#, 'word8ToWord#)
    , ('GHC.word8ToInt8#, 'word8ToInt8#)
    , ('GHC.plusWord8#, 'plusWord8#)
    , ('GHC.subWord8#, 'subWord8#)
    , ('GHC.timesWord8#, 'timesWord8#)
    -- , ('GHC.quotWord8#, 'quotWord8#)
    -- , ('GHC.remWord8#, 'remWord8#)
    -- , ('GHC.quotRemWord8#, 'quotRemWord8#)
    , ('GHC.andWord8#, 'andWord8#)
    , ('GHC.orWord8#, 'orWord8#)
    , ('GHC.xorWord8#, 'xorWord8#)
    , ('GHC.notWord8#, 'notWord8#)
    -- , ('GHC.uncheckedShiftLWord8#, 'uncheckedShiftLWord8#)
    -- , ('GHC.uncheckedShiftRLWord8#, 'uncheckedShiftRLWord8#)
    , ('GHC.eqWord8#, 'eqWord8#)
    , ('GHC.neWord8#, 'neWord8#)
    , ('GHC.geWord8#, 'geWord8#)
    , ('GHC.gtWord8#, 'gtWord8#)
    , ('GHC.leWord8#, 'leWord8#)
    , ('GHC.ltWord8#, 'ltWord8#)

    -- Word16# primitive operations.
    ------------------------------
    , ('GHC.word16ToWord#, 'word16ToWord#)
    , ('GHC.word16ToInt16#, 'word16ToInt16#)
    , ('GHC.plusWord16#, 'plusWord16#)
    , ('GHC.subWord16#, 'subWord16#)
    , ('GHC.timesWord16#, 'timesWord16#)
    -- , ('GHC.quotWord16#, 'quotWord16#)
    -- , ('GHC.remWord16#, 'remWord16#)
    -- , ('GHC.quotRemWord16#, 'quotRemWord16#)
    , ('GHC.andWord16#, 'andWord16#)
    , ('GHC.orWord16#, 'orWord16#)
    , ('GHC.xorWord16#, 'xorWord16#)
    , ('GHC.notWord16#, 'notWord16#)
    -- , ('GHC.uncheckedShiftLWord16#, 'uncheckedShiftLWord16#)
    -- , ('GHC.uncheckedShiftRLWord16#, 'uncheckedShiftRLWord16#)
    , ('GHC.eqWord16#, 'eqWord16#)
    , ('GHC.neWord16#, 'neWord16#)
    , ('GHC.geWord16#, 'geWord16#)
    , ('GHC.gtWord16#, 'gtWord16#)
    , ('GHC.leWord16#, 'leWord16#)
    , ('GHC.ltWord16#, 'ltWord16#)

    -- Word32# primitive operations.
    ------------------------------
    , ('GHC.word32ToWord#, 'word32ToWord#)
    , ('GHC.word32ToInt32#, 'word32ToInt32#)
    , ('GHC.plusWord32#, 'plusWord32#)
    , ('GHC.subWord32#, 'subWord32#)
    , ('GHC.timesWord32#, 'timesWord32#)
    -- , ('GHC.quotWord32#, 'quotWord32#)
    -- , ('GHC.remWord32#, 'remWord32#)
    -- , ('GHC.quotRemWord32#, 'quotRemWord32#)
    , ('GHC.andWord32#, 'andWord32#)
    , ('GHC.orWord32#, 'orWord32#)
    , ('GHC.xorWord32#, 'xorWord32#)
    , ('GHC.notWord32#, 'notWord32#)
    -- , ('GHC.uncheckedShiftLWord32#, 'uncheckedShiftLWord32#)
    -- , ('GHC.uncheckedShiftRLWord32#, 'uncheckedShiftRLWord32#)
    , ('GHC.eqWord32#, 'eqWord32#)
    , ('GHC.neWord32#, 'neWord32#)
    , ('GHC.geWord32#, 'geWord32#)
    , ('GHC.gtWord32#, 'gtWord32#)
    , ('GHC.leWord32#, 'leWord32#)
    , ('GHC.ltWord32#, 'ltWord32#)

    -- Word64# primitive operations.
    ------------------------------
    , ('GHC.word64ToWord#, 'word64ToWord#)
    , ('GHC.word64ToInt64#, 'word64ToInt64#)
    , ('GHC.plusWord64#, 'plusWord64#)
    , ('GHC.subWord64#, 'subWord64#)
    , ('GHC.timesWord64#, 'timesWord64#)
    -- , ('GHC.quotWord64#, 'quotWord64#)
    -- , ('GHC.remWord64#, 'remWord64#)
    , ('GHC.and64#, 'and64#)
    , ('GHC.or64#, 'or64#)
    , ('GHC.xor64#, 'xor64#)
    , ('GHC.not64#, 'not64#)
    -- , ('GHC.uncheckedShiftL64#, 'uncheckedShiftL64#)
    -- , ('GHC.uncheckedShiftRL64#, 'uncheckedShiftRL64#)
    , ('GHC.eqWord64#, 'eqWord64#)
    , ('GHC.neWord64#, 'neWord64#)
    , ('GHC.geWord64#, 'geWord64#)
    , ('GHC.gtWord64#, 'gtWord64#)
    , ('GHC.leWord64#, 'leWord64#)
    , ('GHC.ltWord64#, 'ltWord64#)

    -- Haskell functions without unfoldings.
    ----------------------------------------
    -- NOTE: Ideally we would not have these. It's just that GHC tosses
    -- their unfolding and we cannot get 'base' to be compiled with the flag
    -- 'expose-all-unfoldings' as 'base' is tied to the compiler...
    , ('GHC.integerFromWord#, 'integerFromWord#)
    , ('GHC.integerToWord#, 'integerToWord#)
    , ('GHC.integerFromNatural, 'integerFromNatural)
    , ('GHC.integerToInt#, 'integerToInt#)
    , ('GHC.naturalAdd, 'naturalAdd)
    , ('GHC.naturalSubThrow, 'naturalSubThrow)
    , ('GHC.noinline, 'noinline)
    , ('GHC.undefined, 'undefined)
    , ('GHC.patError, 'patError')
    , ('GHC.withSomeSNat, 'withSomeSNat)
    ]
  }

type BitVecPW = Pantomime.BitVec Pantomime.PlatformWordSize

type BitVec8 = Pantomime.BitVec 8

type BitVec16 = Pantomime.BitVec 16

type BitVec32 = Pantomime.BitVec 32

type BitVec64 = Pantomime.BitVec 64

fromBV
  :: forall r n (a :: TYPE r)
   . Pantomime.Embeddable (Pantomime.BitVec n) a
  => Pantomime.BitVec n
  -> a
fromBV = Pantomime.embed

-- NOTE: Sadly, we cannot create one instance for the 'eq' functions
-- as Haskell does not allow us to be polymorphic over the runtime
-- representation. Probably we can once we adjust the definition of 'Embeddable'
-- to be like 'Coercable'.
--
-- eqBV
--   :: forall r n (a :: TYPE r)
--    . Pantomime.Embeddable (Pantomime.BitVec n) a
--   => a
--   -> a
--   -> Pantomime.Bool
-- eqBV lhs rhs = Pantomime.bveq @64 (Pantomime.project lhs) (Pantomime.project rhs)
--
-- Indeed, perhaps it could work if we could write the following:
-- eqBV = Pantomime.embed $ Pantomime.bveq @n
--
-- As in this case, we do not need to bind the variables.

eqI :: Pantomime.Embeddable BitVec64 Int# => Int# -> Int# -> Pantomime.Bool
eqI lhs rhs = Pantomime.bveq @64 (Pantomime.project lhs) (Pantomime.project rhs)

eqI8 :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Pantomime.Bool
eqI8 lhs rhs = Pantomime.bveq @8 (Pantomime.project lhs) (Pantomime.project rhs)

eqI16 :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Pantomime.Bool
eqI16 lhs rhs = Pantomime.bveq @16 (Pantomime.project lhs) (Pantomime.project rhs)

eqI32 :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Pantomime.Bool
eqI32 lhs rhs = Pantomime.bveq @32 (Pantomime.project lhs) (Pantomime.project rhs)

eqI64 :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Pantomime.Bool
eqI64 lhs rhs = Pantomime.bveq @64 (Pantomime.project lhs) (Pantomime.project rhs)

eqW :: Pantomime.Embeddable BitVec64 Word# => Word# -> Word# -> Pantomime.Bool
eqW lhs rhs = Pantomime.bveq @64 (Pantomime.project lhs) (Pantomime.project rhs)

eqW8 :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Pantomime.Bool
eqW8 lhs rhs = Pantomime.bveq @8 (Pantomime.project lhs) (Pantomime.project rhs)

eqW16 :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Pantomime.Bool
eqW16 lhs rhs = Pantomime.bveq @16 (Pantomime.project lhs) (Pantomime.project rhs)

eqW32 :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Pantomime.Bool
eqW32 lhs rhs = Pantomime.bveq @32 (Pantomime.project lhs) (Pantomime.project rhs)

eqW64 :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Pantomime.Bool
eqW64 lhs rhs = Pantomime.bveq @64 (Pantomime.project lhs) (Pantomime.project rhs)

bool2I# :: Pantomime.Bool -> Int#
bool2I# scrut = Pantomime.iteIP scrut 1# 0#

tagToEnum
  :: forall a
   . Pantomime.Embeddable BitVecPW Int#
  => Int#
  -> a
tagToEnum i = Pantomime.tagToEnum $ Pantomime.project i

dataToTag
  :: forall l (a :: TYPE (BoxedRep l))
   . Pantomime.Embeddable BitVecPW Int#
  => a
  -> Int#
-- SAFETY: We need some 'unsafeCoerce' magic because we cannot bind a type
-- without a fixed runtime representation. The symbolic evaluator doesn't care
-- at all about 'RuntimeRep' and so we can just fake it to be 'Lifted'.
-- Perhaps once embed becomes more like coerce that we can do the following:
-- dataToTag = Pantomime.embed Pantomime.dataToTag
dataToTag = unsafeCoerce @(forall b. b -> Int#) @(forall b. b -> Int#) go
  where
    go :: forall b. b -> Int#
    go x = Pantomime.embed @_ @_ @BitVecPW $ Pantomime.dataToTag x

int2Word#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVecPW Word#
  => Int#
  -> Word#
int2Word# x = Pantomime.embed @_ @_ @BitVecPW $ Pantomime.project x

intToInt8#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVec8 Int8#
  => Int#
  -> Int8#
intToInt8# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvselect @0 @8 @Pantomime.PlatformWordSize x'

intToInt16#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVec16 Int16#
  => Int#
  -> Int16#
intToInt16# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvselect @0 @16 @Pantomime.PlatformWordSize x'

intToInt32#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVec32 Int32#
  => Int#
  -> Int32#
intToInt32# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvselect @0 @32 @Pantomime.PlatformWordSize x'

intToInt64#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVec64 Int64#
  => Int#
  -> Int64#
intToInt64# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvsresize @Pantomime.PlatformWordSize @64 x'

binaryInt#
  :: Pantomime.Embeddable BitVecPW Int#
  => (BitVecPW -> BitVecPW -> BitVecPW)
  -> Int#
  -> Int#
  -> Int#
binaryInt# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

(+#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(+#) = binaryInt# (+)

(-#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(-#) = binaryInt# (-)

(*#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(*#) = binaryInt# (*)

binaryIntC#
  :: Pantomime.Embeddable BitVecPW Int#
  => (forall n. KnownNat n => Pantomime.BitVec n -> Pantomime.BitVec n -> Pantomime.BitVec n)
  -> Int#
  -> Int#
  -> (# Int#, Int# #)
binaryIntC# f lhs rhs = do
  let project' x
        = Pantomime.bvzext @_ @(Pantomime.PlatformWordSize + 1)
        $ Pantomime.project @_ @_ @BitVecPW @Int# x
  let lhs' = project' lhs
  let rhs' = project' rhs

  let result = f lhs' rhs'
  let add = Pantomime.bvselect @0 @Pantomime.PlatformWordSize result
  let carry = Pantomime.bvselect @Pantomime.PlatformWordSize @1 result
  let carry' = Pantomime.bvzext @_ @Pantomime.PlatformWordSize carry
  (# Pantomime.embed add, Pantomime.embed carry' #)

addIntC#
  :: Pantomime.Embeddable BitVecPW Int#
  => Int#
  -> Int#
  -> (# Int#, Int# #)
addIntC# = binaryIntC# Pantomime.bvadd

subIntC#
  :: Pantomime.Embeddable BitVecPW Int#
  => Int#
  -> Int#
  -> (# Int#, Int# #)
subIntC# = binaryIntC# \lhs rhs -> Pantomime.bvadd lhs (Pantomime.bvneg rhs)

andI# :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
andI# = binaryInt# Pantomime.bvand

orI# :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
orI# = binaryInt# Pantomime.bvor

xorI# :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
xorI# = binaryInt# Pantomime.bvxor

unaryInt#
  :: Pantomime.Embeddable BitVecPW Int#
  => (BitVecPW -> BitVecPW)
  -> Int#
  -> Int#
unaryInt# f x = do
  let x' = Pantomime.project x
  Pantomime.embed $ f x'

notI# :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int#
notI# = unaryInt# Pantomime.bvnot

negateInt# :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int#
negateInt# = unaryInt# Pantomime.bvneg

compareInt#
  :: Pantomime.Embeddable BitVecPW Int#
  => (BitVecPW -> BitVecPW -> Pantomime.Bool)
  -> Int#
  -> Int#
  -> Int#
compareInt# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

(==#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(==#) = compareInt# Pantomime.bveq

(/=#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(/=#) = compareInt# Pantomime.bvneq

(>=#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(>=#) = compareInt# $ flip Pantomime.bvsle

(>#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(>#) = compareInt# $ flip Pantomime.bvslt

(<=#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(<=#) = compareInt# Pantomime.bvsle

(<#) :: Pantomime.Embeddable BitVecPW Int# => Int# -> Int# -> Int#
(<#) = compareInt# Pantomime.bvslt

int8ToInt#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVec8 Int8#
  => Int8#
  -> Int#
int8ToInt# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvsext @8 @Pantomime.PlatformWordSize x'

int8ToWord8#
  :: Pantomime.Embeddable BitVec8 Int8#
  => Pantomime.Embeddable BitVec8 Word8#
  => Int8#
  -> Word8#
int8ToWord8# x = Pantomime.embed @_ @_ @BitVec8 $ Pantomime.project x

binaryInt8#
  :: Pantomime.Embeddable BitVec8 Int8#
  => (BitVec8 -> BitVec8 -> BitVec8)
  -> Int8#
  -> Int8#
  -> Int8#
binaryInt8# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int8#
plusInt8# = binaryInt8# (+)

subInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int8#
subInt8# = binaryInt8# (-)

timesInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int8#
timesInt8# = binaryInt8# (*)

unaryInt8#
  :: Pantomime.Embeddable BitVec8 Int8#
  => (BitVec8 -> BitVec8)
  -> Int8#
  -> Int8#
unaryInt8# f x = do
  let x' = Pantomime.project x
  Pantomime.embed $ f x'

negateInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8#
negateInt8# = unaryInt8# negate

compareInt8#
  :: Pantomime.Embeddable BitVec8 Int8#
  => (BitVec8 -> BitVec8 -> Pantomime.Bool)
  -> Int8#
  -> Int8#
  -> Int#
compareInt8# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int#
eqInt8# = compareInt8# Pantomime.bveq

neInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int#
neInt8# = compareInt8# Pantomime.bvneq

geInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int#
geInt8# = compareInt8# $ flip Pantomime.bvsle

gtInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int#
gtInt8# = compareInt8# $ flip Pantomime.bvslt

leInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int#
leInt8# = compareInt8# Pantomime.bvsle

ltInt8# :: Pantomime.Embeddable BitVec8 Int8# => Int8# -> Int8# -> Int#
ltInt8# = compareInt8# Pantomime.bvslt

int16ToInt#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVec16 Int16#
  => Int16#
  -> Int#
int16ToInt# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvsext @16 @Pantomime.PlatformWordSize x'

int16ToWord16#
  :: Pantomime.Embeddable BitVec16 Int16#
  => Pantomime.Embeddable BitVec16 Word16#
  => Int16#
  -> Word16#
int16ToWord16# x = Pantomime.embed @_ @_ @BitVec16 $ Pantomime.project x

binaryInt16#
  :: Pantomime.Embeddable BitVec16 Int16#
  => (BitVec16 -> BitVec16 -> BitVec16)
  -> Int16#
  -> Int16#
  -> Int16#
binaryInt16# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int16#
plusInt16# = binaryInt16# (+)

subInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int16#
subInt16# = binaryInt16# (-)

timesInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int16#
timesInt16# = binaryInt16# (*)

unaryInt16#
  :: Pantomime.Embeddable BitVec16 Int16#
  => (BitVec16 -> BitVec16)
  -> Int16#
  -> Int16#
unaryInt16# f x = do
  let x' = Pantomime.project x
  Pantomime.embed $ f x'

negateInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16#
negateInt16# = unaryInt16# negate

compareInt16#
  :: Pantomime.Embeddable BitVec16 Int16#
  => (BitVec16 -> BitVec16 -> Pantomime.Bool)
  -> Int16#
  -> Int16#
  -> Int#
compareInt16# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int#
eqInt16# = compareInt16# Pantomime.bveq

neInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int#
neInt16# = compareInt16# Pantomime.bvneq

geInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int#
geInt16# = compareInt16# $ flip Pantomime.bvsle

gtInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int#
gtInt16# = compareInt16# $ flip Pantomime.bvslt

leInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int#
leInt16# = compareInt16# Pantomime.bvsle

ltInt16# :: Pantomime.Embeddable BitVec16 Int16# => Int16# -> Int16# -> Int#
ltInt16# = compareInt16# Pantomime.bvslt

int32ToInt#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVec32 Int32#
  => Int32#
  -> Int#
int32ToInt# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvsext @32 @Pantomime.PlatformWordSize x'

int32ToWord32#
  :: Pantomime.Embeddable BitVec32 Int32#
  => Pantomime.Embeddable BitVec32 Word32#
  => Int32#
  -> Word32#
int32ToWord32# x = Pantomime.embed @_ @_ @BitVec32 $ Pantomime.project x

binaryInt32#
  :: Pantomime.Embeddable BitVec32 Int32#
  => (BitVec32 -> BitVec32 -> BitVec32)
  -> Int32#
  -> Int32#
  -> Int32#
binaryInt32# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int32#
plusInt32# = binaryInt32# (+)

subInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int32#
subInt32# = binaryInt32# (-)

timesInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int32#
timesInt32# = binaryInt32# (*)

unaryInt32#
  :: Pantomime.Embeddable BitVec32 Int32#
  => (BitVec32 -> BitVec32)
  -> Int32#
  -> Int32#
unaryInt32# f x = do
  let x' = Pantomime.project x
  Pantomime.embed $ f x'

negateInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32#
negateInt32# = unaryInt32# negate

compareInt32#
  :: Pantomime.Embeddable BitVec32 Int32#
  => (BitVec32 -> BitVec32 -> Pantomime.Bool)
  -> Int32#
  -> Int32#
  -> Int#
compareInt32# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int#
eqInt32# = compareInt32# Pantomime.bveq

neInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int#
neInt32# = compareInt32# Pantomime.bvneq

geInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int#
geInt32# = compareInt32# $ flip Pantomime.bvsle

gtInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int#
gtInt32# = compareInt32# $ flip Pantomime.bvslt

leInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int#
leInt32# = compareInt32# Pantomime.bvsle

ltInt32# :: Pantomime.Embeddable BitVec32 Int32# => Int32# -> Int32# -> Int#
ltInt32# = compareInt32# Pantomime.bvslt

int64ToInt#
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Embeddable BitVec64 Int64#
  => Int64#
  -> Int#
int64ToInt# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvsresize @64 @Pantomime.PlatformWordSize x'

int64ToWord64#
  :: Pantomime.Embeddable BitVec64 Int64#
  => Pantomime.Embeddable BitVec64 Word64#
  => Int64#
  -> Word64#
int64ToWord64# x = Pantomime.embed @_ @_ @BitVec64 $ Pantomime.project x

binaryInt64#
  :: Pantomime.Embeddable BitVec64 Int64#
  => (BitVec64 -> BitVec64 -> BitVec64)
  -> Int64#
  -> Int64#
  -> Int64#
binaryInt64# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int64#
plusInt64# = binaryInt64# (+)

subInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int64#
subInt64# = binaryInt64# (-)

timesInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int64#
timesInt64# = binaryInt64# (*)

unaryInt64#
  :: Pantomime.Embeddable BitVec64 Int64#
  => (BitVec64 -> BitVec64)
  -> Int64#
  -> Int64#
unaryInt64# f x = do
  let x' = Pantomime.project x
  Pantomime.embed $ f x'

negateInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64#
negateInt64# = unaryInt64# negate

compareInt64#
  :: Pantomime.Embeddable BitVec64 Int64#
  => (BitVec64 -> BitVec64 -> Pantomime.Bool)
  -> Int64#
  -> Int64#
  -> Int#
compareInt64# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int#
eqInt64# = compareInt64# Pantomime.bveq

neInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int#
neInt64# = compareInt64# Pantomime.bvneq

geInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int#
geInt64# = compareInt64# $ flip Pantomime.bvsle

gtInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int#
gtInt64# = compareInt64# $ flip Pantomime.bvslt

leInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int#
leInt64# = compareInt64# Pantomime.bvsle

ltInt64# :: Pantomime.Embeddable BitVec64 Int64# => Int64# -> Int64# -> Int#
ltInt64# = compareInt64# Pantomime.bvslt

word2Int#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVecPW Int#
  => Word#
  -> Int#
word2Int# x = Pantomime.embed @_ @_ @BitVecPW $ Pantomime.project x

wordToWord8#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVec8 Word8#
  => Word#
  -> Word8#
wordToWord8# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvselect @0 @8 @Pantomime.PlatformWordSize x'

wordToWord16#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVec16 Word16#
  => Word#
  -> Word16#
wordToWord16# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvselect @0 @16 @Pantomime.PlatformWordSize x'

wordToWord32#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVec32 Word32#
  => Word#
  -> Word32#
wordToWord32# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvselect @0 @32 @Pantomime.PlatformWordSize x'

wordToWord64#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVec64 Word64#
  => Word#
  -> Word64#
wordToWord64# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvzresize @Pantomime.PlatformWordSize @64 x'

binaryWord#
  :: Pantomime.Embeddable BitVecPW Word#
  => (BitVecPW -> BitVecPW -> BitVecPW)
  -> Word#
  -> Word#
  -> Word#
binaryWord# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusWord# :: Pantomime.Embeddable BitVecPW Word# => Word# -> Word# -> Word#
plusWord# = binaryWord# (+)

minusWord# :: Pantomime.Embeddable BitVecPW Word# => Word# -> Word# -> Word#
minusWord# = binaryWord# (-)

timesWord# :: Pantomime.Embeddable BitVecPW Word# => Word# -> Word# -> Word#
timesWord# = binaryWord# (*)

binaryWordC#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVecPW Int#
  => (forall n. KnownNat n => Pantomime.BitVec n -> Pantomime.BitVec n -> Pantomime.BitVec n)
  -> Word#
  -> Word#
  -> (# Word#, Int# #)
binaryWordC# f lhs rhs = do
  let project' x
        = Pantomime.bvzext @_ @(Pantomime.PlatformWordSize + 1)
        $ Pantomime.project @_ @_ @BitVecPW @Word# x
  let lhs' = project' lhs
  let rhs' = project' rhs

  let result = f lhs' rhs'
  let add = Pantomime.bvselect @0 @Pantomime.PlatformWordSize result
  let carry = Pantomime.bvselect @Pantomime.PlatformWordSize @1 result
  let carry' = Pantomime.bvzext @_ @Pantomime.PlatformWordSize carry
  (# Pantomime.embed add, Pantomime.embed carry' #)

addWordC#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVecPW Int#
  => Word#
  -> Word#
  -> (# Word#, Int# #)
addWordC# = binaryWordC# Pantomime.bvadd

subWordC#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVecPW Int#
  => Word#
  -> Word#
  -> (# Word#, Int# #)
subWordC# = binaryWordC# \lhs rhs -> Pantomime.bvadd lhs (Pantomime.bvneg rhs)

and# :: Pantomime.Embeddable BitVecPW Word# => Word# -> Word# -> Word#
and# = binaryWord# Pantomime.bvand

or# :: Pantomime.Embeddable BitVecPW Word# => Word# -> Word# -> Word#
or# = binaryWord# Pantomime.bvor

xor# :: Pantomime.Embeddable BitVecPW Word# => Word# -> Word# -> Word#
xor# = binaryWord# Pantomime.bvxor

not# :: Pantomime.Embeddable BitVecPW Word# => Word# -> Word#
not# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvnot @Pantomime.PlatformWordSize x'

-- FIXME: This behaviour is not great: it is UB when the idx is out of bounds
-- but we now give it a specific semantic. Ideally, we would have something like
-- "forall UB that a shift can produce". This would probably amount to an
-- uninterpreted function for the shift. I don't have a way of conjuring this
-- at the moment, so I'll leave it as is for now!
uncheckedShiftRL#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVecPW Int#
  => Word#
  -> Int#
  -> Word#
uncheckedShiftRL# val idx = do
  let val' = Pantomime.project val
  let idx' = Pantomime.project idx
  Pantomime.embed $ Pantomime.bvlshr @Pantomime.PlatformWordSize val' idx'

compareWord#
  :: Pantomime.Embeddable BitVecPW Word#
  => (BitVecPW -> BitVecPW -> Pantomime.Bool)
  -> Word#
  -> Word#
  -> Int#
compareWord# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqWord# :: Pantomime.Embeddable BitVec64 Word# => Word# -> Word# -> Int#
eqWord# = compareWord# Pantomime.bveq

neWord# :: Pantomime.Embeddable BitVec64 Word# => Word# -> Word# -> Int#
neWord# = compareWord# Pantomime.bvneq

geWord# :: Pantomime.Embeddable BitVec64 Word# => Word# -> Word# -> Int#
geWord# = compareWord# $ flip Pantomime.bvule

gtWord# :: Pantomime.Embeddable BitVec64 Word# => Word# -> Word# -> Int#
gtWord# = compareWord# $ flip Pantomime.bvult

leWord# :: Pantomime.Embeddable BitVec64 Word# => Word# -> Word# -> Int#
leWord# = compareWord# Pantomime.bvule

ltWord# :: Pantomime.Embeddable BitVec64 Word# => Word# -> Word# -> Int#
ltWord# = compareWord# Pantomime.bvult

word8ToWord#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVec8 Word8#
  => Word8#
  -> Word#
word8ToWord# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvzext @8 @Pantomime.PlatformWordSize x'

word8ToInt8#
  :: Pantomime.Embeddable BitVec8 Word8#
  => Pantomime.Embeddable BitVec8 Int8#
  => Word8#
  -> Int8#
word8ToInt8# x = Pantomime.embed @_ @_ @BitVec8 $ Pantomime.project x

binaryWord8#
  :: Pantomime.Embeddable BitVec8 Word8#
  => (BitVec8 -> BitVec8 -> BitVec8)
  -> Word8#
  -> Word8#
  -> Word8#
binaryWord8# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Word8#
plusWord8# = binaryWord8# (+)

subWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Word8#
subWord8# = binaryWord8# (-)

timesWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Word8#
timesWord8# = binaryWord8# (*)

andWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Word8#
andWord8# = binaryWord8# Pantomime.bvand

orWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Word8#
orWord8# = binaryWord8# Pantomime.bvor

xorWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Word8#
xorWord8# = binaryWord8# Pantomime.bvxor

notWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8#
notWord8# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvnot @8 x'

compareWord8#
  :: Pantomime.Embeddable BitVec8 Word8#
  => (BitVec8 -> BitVec8 -> Pantomime.Bool)
  -> Word8#
  -> Word8#
  -> Int#
compareWord8# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Int#
eqWord8# = compareWord8# Pantomime.bveq

neWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Int#
neWord8# = compareWord8# Pantomime.bvneq

geWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Int#
geWord8# = compareWord8# $ flip Pantomime.bvule

gtWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Int#
gtWord8# = compareWord8# $ flip Pantomime.bvult

leWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Int#
leWord8# = compareWord8# Pantomime.bvule

ltWord8# :: Pantomime.Embeddable BitVec8 Word8# => Word8# -> Word8# -> Int#
ltWord8# = compareWord8# Pantomime.bvult

word16ToWord#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVec16 Word16#
  => Word16#
  -> Word#
word16ToWord# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvzext @16 @Pantomime.PlatformWordSize x'

word16ToInt16#
  :: Pantomime.Embeddable BitVec16 Word16#
  => Pantomime.Embeddable BitVec16 Int16#
  => Word16#
  -> Int16#
word16ToInt16# x = Pantomime.embed @_ @_ @BitVec16 $ Pantomime.project x

binaryWord16#
  :: Pantomime.Embeddable BitVec16 Word16#
  => (BitVec16 -> BitVec16 -> BitVec16)
  -> Word16#
  -> Word16#
  -> Word16#
binaryWord16# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Word16#
plusWord16# = binaryWord16# (+)

subWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Word16#
subWord16# = binaryWord16# (-)

timesWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Word16#
timesWord16# = binaryWord16# (*)

andWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Word16#
andWord16# = binaryWord16# Pantomime.bvand

orWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Word16#
orWord16# = binaryWord16# Pantomime.bvor

xorWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Word16#
xorWord16# = binaryWord16# Pantomime.bvxor

notWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16#
notWord16# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvnot @16 x'

compareWord16#
  :: Pantomime.Embeddable BitVec16 Word16#
  => (BitVec16 -> BitVec16 -> Pantomime.Bool)
  -> Word16#
  -> Word16#
  -> Int#
compareWord16# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Int#
eqWord16# = compareWord16# Pantomime.bveq

neWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Int#
neWord16# = compareWord16# Pantomime.bvneq

geWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Int#
geWord16# = compareWord16# $ flip Pantomime.bvule

gtWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Int#
gtWord16# = compareWord16# $ flip Pantomime.bvult

leWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Int#
leWord16# = compareWord16# Pantomime.bvule

ltWord16# :: Pantomime.Embeddable BitVec16 Word16# => Word16# -> Word16# -> Int#
ltWord16# = compareWord16# Pantomime.bvult

word32ToWord#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVec32 Word32#
  => Word32#
  -> Word#
word32ToWord# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvzext @32 @Pantomime.PlatformWordSize x'

word32ToInt32#
  :: Pantomime.Embeddable BitVec32 Word32#
  => Pantomime.Embeddable BitVec32 Int32#
  => Word32#
  -> Int32#
word32ToInt32# x = Pantomime.embed @_ @_ @BitVec32 $ Pantomime.project x

binaryWord32#
  :: Pantomime.Embeddable BitVec32 Word32#
  => (BitVec32 -> BitVec32 -> BitVec32)
  -> Word32#
  -> Word32#
  -> Word32#
binaryWord32# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Word32#
plusWord32# = binaryWord32# (+)

subWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Word32#
subWord32# = binaryWord32# (-)

timesWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Word32#
timesWord32# = binaryWord32# (*)

andWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Word32#
andWord32# = binaryWord32# Pantomime.bvand

orWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Word32#
orWord32# = binaryWord32# Pantomime.bvor

xorWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Word32#
xorWord32# = binaryWord32# Pantomime.bvxor

notWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32#
notWord32# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvnot @32 x'

compareWord32#
  :: Pantomime.Embeddable BitVec32 Word32#
  => (BitVec32 -> BitVec32 -> Pantomime.Bool)
  -> Word32#
  -> Word32#
  -> Int#
compareWord32# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Int#
eqWord32# = compareWord32# Pantomime.bveq

neWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Int#
neWord32# = compareWord32# Pantomime.bvneq

geWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Int#
geWord32# = compareWord32# $ flip Pantomime.bvule

gtWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Int#
gtWord32# = compareWord32# $ flip Pantomime.bvult

leWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Int#
leWord32# = compareWord32# Pantomime.bvule

ltWord32# :: Pantomime.Embeddable BitVec32 Word32# => Word32# -> Word32# -> Int#
ltWord32# = compareWord32# Pantomime.bvult

word64ToWord#
  :: Pantomime.Embeddable BitVecPW Word#
  => Pantomime.Embeddable BitVec64 Word64#
  => Word64#
  -> Word#
word64ToWord# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvzresize @64 @Pantomime.PlatformWordSize x'

word64ToInt64#
  :: Pantomime.Embeddable BitVec64 Word64#
  => Pantomime.Embeddable BitVec64 Int64#
  => Word64#
  -> Int64#
word64ToInt64# x = Pantomime.embed @_ @_ @BitVec64 $ Pantomime.project x

binaryWord64#
  :: Pantomime.Embeddable BitVec64 Word64#
  => (BitVec64 -> BitVec64 -> BitVec64)
  -> Word64#
  -> Word64#
  -> Word64#
binaryWord64# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  Pantomime.embed $ f lhs' rhs'

plusWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Word64#
plusWord64# = binaryWord64# (+)

subWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Word64#
subWord64# = binaryWord64# (-)

timesWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Word64#
timesWord64# = binaryWord64# (*)

and64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Word64#
and64# = binaryWord64# Pantomime.bvand

or64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Word64#
or64# = binaryWord64# Pantomime.bvor

xor64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Word64#
xor64# = binaryWord64# Pantomime.bvxor

not64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64#
not64# x = do
  let x' = Pantomime.project x
  Pantomime.embed $ Pantomime.bvnot @64 x'

compareWord64#
  :: Pantomime.Embeddable BitVec64 Word64#
  => (BitVec64 -> BitVec64 -> Pantomime.Bool)
  -> Word64#
  -> Word64#
  -> Int#
compareWord64# f lhs rhs = do
  let lhs' = Pantomime.project lhs
  let rhs' = Pantomime.project rhs
  bool2I# $ f lhs' rhs'

eqWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Int#
eqWord64# = compareWord64# Pantomime.bveq

neWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Int#
neWord64# = compareWord64# Pantomime.bvneq

geWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Int#
geWord64# = compareWord64# $ flip Pantomime.bvule

gtWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Int#
gtWord64# = compareWord64# $ flip Pantomime.bvult

leWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Int#
leWord64# = compareWord64# Pantomime.bvule

ltWord64# :: Pantomime.Embeddable BitVec64 Word64# => Word64# -> Word64# -> Int#
ltWord64# = compareWord64# Pantomime.bvult

hsi2i
  :: Pantomime.Embeddable BitVecPW Int#
  => Integer
  -> Pantomime.Integer
hsi2i = \case
  IS x -> Pantomime.bv2i @Pantomime.PlatformWordSize $ Pantomime.project x
  IP _x -> undefined
  IN _x -> undefined

i2hsi
  :: Pantomime.Embeddable BitVecPW Int#
  => Pantomime.Integer
  -> Integer
i2hsi x = do
  let toI (I# i) = Pantomime.bv2i $ Pantomime.project @_ @_ @BitVecPW i
  let minI = toI minBound
  let maxI = toI maxBound
  if
    -- TODO: We should actually implement the 'undefined'. It depends on the
    -- interpretation of ByteArray# though, which we currently do not use. Same
    -- for the inverse function btw.
    | x < minI -> undefined
    | maxI < x -> undefined
    | otherwise -> do
      let x' = Pantomime.i2bv @Pantomime.PlatformWordSize x
      IS $ Pantomime.embed x'

-- TODO: The below definitions exists solely because the unfolding doesn't
-- exist. There should be a way around this...

integerFromNatural :: Natural -> Integer
integerFromNatural (NS x) = GHC.integerFromWord# x
integerFromNatural (NB x) = IP x

integerFromWord# :: Word# -> Integer
integerFromWord# w = if
  | let i = GHC.word2Int# w
  , GHC.isTrue# (i GHC.>=# 0#) -> IS i
  | otherwise -> IP (GHC.bigNatFromWord# w)

integerToInt# :: Integer -> Int#
integerToInt# = \case
  IS i -> i
  IP b -> GHC.word2Int# $ GHC.bigNatToWord# b
  IN b -> GHC.negateInt# $ GHC.word2Int# $ GHC.bigNatToWord# b

integerToWord# :: Integer -> Word#
integerToWord# = \case
  IS i -> GHC.int2Word# i
  IP bn -> GHC.bigNatToWord# bn
  IN bn -> GHC.int2Word# $ GHC.negateInt# $ GHC.word2Int# $ GHC.bigNatToWord# bn

naturalAdd :: Natural -> Natural -> Natural
naturalAdd = \cases
  (NS x) (NB y) -> NB $ GHC.bigNatAddWord# y x
  (NB x) (NS y) -> NB $ GHC.bigNatAddWord# x y
  (NB x) (NB y) -> NB $ GHC.bigNatAdd x y
  (NS x) (NS y) -> case GHC.addWordC# x y of
    (# l, 0# #) -> NS l
    (# l, c  #) -> NB $ GHC.bigNatFromWord2# (GHC.int2Word# c) l

naturalSubThrow :: Natural -> Natural -> Natural
naturalSubThrow (NS _) (NB _) = GHC.raiseUnderflow
naturalSubThrow (NB x) (NS y) = GHC.naturalFromBigNat# $ GHC.bigNatSubWordUnsafe# x y
naturalSubThrow (NS x) (NS y) = case GHC.subWordC# x y of
  (# l,0# #) -> NS l
  (# _,_  #) -> GHC.raiseUnderflow
naturalSubThrow (NB x) (NB y) = case GHC.bigNatSub x y of
  (# (# #) |   #) -> GHC.raiseUnderflow
  (#       | z #) -> GHC.naturalFromBigNat# z

noinline :: a -> a
noinline = id

-- FIXME: This is not actually the implementation for 'undefined'.
undefined :: a
undefined = GHC.raise# ()

-- FIXME: This is not actually the implementation for 'patError'.
patError' :: forall q (a :: TYPE q). Addr# -> a
patError' _ = GHC.raise# ()

withSomeSNat
  :: forall rep (r :: TYPE rep)
   . Natural
  -> (forall n. SNat n -> r)
  -> r
withSomeSNat n f = f $ unsafeSNat n
