-- {-# LANGUAGE Strict #-}
-- {-# LANGUAGE UnliftedDatatypes #-}
-- {-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE GADTs #-}
-- {-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}

module Main
  ( main
  , adder
  , leak
  , obs
  , sim
  , proj
  , theory
  , test
  -- , test2
  ) where

-- import ProcessorControl (test)
-- import GHC.Num.Integer

-- import Data.Bits
-- import GHC.Base

-- import UC
-- import ProcessorControl (runDiff)
-- -- import Data.Word

-- import qualified Projection
-- -- import GHC.Base (Int64#, uncheckedIShiftRA64#)
-- import GHC.Base (Int#, (+#), Word (..), word2Int#, int2Word#, (-#), Int (..))
-- import GHC.Base (Int#, (+#), Int (..))
import GHC.Base
  ( Coercible
  , TYPE
  , RuntimeRep (..)
  , Type
  , Int (..)
  , Int#
  , Int8#
  , Word#
  , raiseOverflow#
  , raise#
  , plusInt8#
  , coerce
  , tagToEnum#
  , word2Int#
  , negateInt#
  , word2Int#
  , int2Word#
  )
import GHC.Int (Int8 (..))
import Data.Typeable
import GHC.TypeNats (Nat, KnownNat, type (+))
import Data.Bits (Bits (..), FiniteBits (..))
import GHC.Num.Integer
  ( integerToInt#
  , integerToWord#
  , Integer (..)
  )
import GHC.Num.BigNat (bigNatToWord#)

import GHC.Exts (IsList (..))

import Prelude
import Pantomime
import Pantomime.Primitive.BitVector qualified as Pantomime
import Pantomime.Clash qualified as Clash (axioms)
import Pantomime.Base qualified as Base (axioms)
import Pantomime.Axiom (PluginAxioms (..))
-- import Pantomime.Primitive.BitVector (BitVector)
-- import Pantomime.Primitive.BitVector qualified as BitVector
import Control.Monad.State

import Clash.Sized.Internal.BitVector (BitVector)
import Clash.Sized.Internal.Unsigned (Unsigned)
import Clash.Sized.Internal.Signed
  ( Signed
  , (+#)
  , (-#)
  , (*#)
  , negate#
  , complement#
  , and#
  , or#
  , xor#
  , abs#
  , eq#
  , neq#
  , lt#
  , le#
  , gt#
  , ge#
  , shiftL#
  , shiftR#
  , fromInteger#
  , unpack#
  , pack#
  , size#
  )
import Grisette (BitCast(..))
import Clash.Prelude (bitCoerce, Resize (..), (++#), slice, d2, d3, msb)

import Core2 qualified
import Control.Monad (void)
import Data.Maybe (isJust)

-- import Numeric (showHex)
-- -- import GHC.Base (Int64#, uncheckedIShiftRL64#)
-- -- import GHC.Base (Int64#, uncheckedIShiftL64#)
-- -- import GHC.Base (Int64#, plusInt64#, intToInt64#, uncheckedIShiftRA64#)
-- -- import GHC.Base (Int64#, plusInt64#)
-- import GHC.Base (Int64#, plusInt64#, quotInt64#)
-- import GHC.Int (Int64(..))

-- {-# ANN adder Spec
--   { observation' = 'obs
--   , leakage' = 'leak
--   , simulator' = 'sim
--   , projection' = 'proj
--   } #-}
-- adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
-- adder s i = case i of
--   Just (a, b) -> (Just $ a + b, s)
--   Nothing -> (Nothing, s)

-- -- {-# ANN compImpl UCNorm #-}
-- -- compImpl :: Maybe Int -> Maybe (Int, Int) -> (((), Maybe Bool), Maybe Bool)
-- -- compImpl = sproj proj $ oproj obs adder

-- -- {-# ANN compSim UCNorm #-}
-- -- compSim :: Maybe Int -> Maybe (Int, Int) -> (((), Maybe Bool), Maybe Bool)
-- -- compSim = sproj' proj $ iproj leak sim

-- obs :: Circuit () (Maybe Int) (Maybe Bool)
-- obs = stateless obs'

-- leak :: Circuit () (Maybe (Int, Int)) (Maybe Bool)
-- leak = stateless leak'

-- obs' :: Maybe Int -> Maybe Bool
-- obs' (Just x) = Just $ x == 0
-- obs' _ = Nothing

-- leak' :: Maybe (Int, Int) -> Maybe Bool
-- leak' (Just (a, b)) = Just $ a + b == 0
-- leak' _ = Nothing

-- sim :: Maybe Bool -> Maybe Bool -> (Maybe Bool, Maybe Bool)
-- sim s i = (i, s)

-- proj :: (Maybe Int, ()) -> ((), Maybe Bool)
-- proj (s, _) = ((), obs' s)

-- stateless :: (a -> b) -> Circuit () a b
-- stateless f _ i = ((), f i)

-- import Clash.Prelude

-- {-# ANN adder Pantomime
--   { observation = 'obs
--   , leakage = 'leak
--   , simulator = 'sim
--   , projection = 'proj
--   } #-}

-- {-# ANN theory (Theory mempty) #-}
-- {-# ANN theory (Theory
--   PluginAxioms
--     { typeAxioms = mempty
--     , termAxioms = fromList
--       [ ('integerToInt#, 'integerToInt')
--       , ('integerToWord#, 'integerToWord')
--       ]
--     }) #-}
-- {-# ANN theory (Theory $ Base.axioms <> Clash.axioms) #-}
theory :: Maybe Int -> Maybe (Int, Int) -> Bool
theory = pantomime Pantomime
  { observation = obs'
  , implementation = adder
  , leakage = leak
  , simulator = sim
  , projection = proj
  }
-- test :: Maybe Int -> Maybe (Int, Int) -> Bool
-- test s i = adder s i == adder s i

-- {-# ANN adder (Theory Base.axioms) #-}
adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
adder s i = swap $ runState (adder' i) s

adder' :: Num a => Maybe (a, a) -> State (Maybe a) (Maybe a)
adder' i = do
  s <- get
  put case i of
    Just (a, b) -> Just (a + b)
    Nothing -> Nothing
  pure s

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

obs :: Num a => Eq a => Circuit () (Maybe a) (Maybe Bool)
obs = stateless obs'

obs' :: Num a => Eq a => Maybe a -> Maybe Bool
obs' (Just x) = Just $ x == 0
obs' _ = Nothing

leak :: Num a => Eq a => Circuit () (Maybe (a, a)) (Maybe Bool)
leak = stateless leak'

leak' :: Num a => Eq a => Maybe (a, a) -> Maybe Bool
-- leak' (Just (a, b)) = Just $ a + b == 0
leak' (Just (a, b)) = Just $ a + b == 1
leak' _ = Nothing

sim :: Maybe Bool -> Maybe Bool -> (Maybe Bool, Maybe Bool)
sim s i = (i, s)

-- proj :: Num a => Eq a => (Maybe a, ()) -> ((), Maybe Bool)
-- proj (s, _) = ((), obs' s)

proj :: Num a => Eq a => Maybe a -> ((), Maybe Bool)
proj s = ((), obs' s)

stateless :: (a -> b) -> Circuit () a b
stateless f _ i = ((), f i)

-- data Exist where
--   Exist :: Wow a => a -> Exist

-- class Wow a where
--   wow :: a -> Bool

-- instance Wow Bool where
--   wow = id

-- instance Wow () where
--   wow _ = True

-- newtype 

-- {-# ANN test (SymCompare 'test) #-}
-- test :: Bool -> Bool
-- test x = do
--   let y = case x of
--         True -> Exist True
--         False -> Exist ()
--   case y of
--     Exist @a z -> wow z

-- test :: Bool -> Exist
-- test = \case
--   True -> Exist True
--   False -> Exist ()

-- data GADT a where
--   D0 :: Bool -> GADT Bool
--   D1 :: a -> GADT a

-- data T where
--   MkT :: forall a (b :: TYPE (TupleRep '[])). ((a, Bool) ~ (Bool, Bool)) => T


-- {-# ANN test (SymCompare 'test) #-}
-- test :: T
-- test = MkT


-- data Foo a where
--   MkFoo :: forall a b. (a ~ b) => Foo a

-- newtype MyBool = MyBool Bool

-- {-# ANN test (SymCompare 'test) #-}
-- test :: Foo Bool
-- test = MkFoo @Bool @Bool

-- data Foo a where
--   MkFoo :: forall a (c :: a ~# Bool). c => Foo a

-- {-# ANN test (SymCompare 'test) #-}
-- test :: Foo Bool
-- test = MkFoo @Bool
-- data a :~: b where
--   Refl :: a :~: a

-- {-# ANN test (SymCompare 'test) #-}
-- test :: Bool :~: Bool
-- test = Refl

-- data RepBool where
--   RepBool :: (a ~ Bool) => RepBool

-- newtype MyBool = MyBool Bool

newtype Test n where
  Test :: Signed n -> Test n
  deriving (Num, Eq, Bits)

-- {-# ANN test (Theory $ Base.axioms <> Clash.axioms) #-}
-- test :: Test (3 + 2) -> Test 5 -> Bool
-- test x y = x .&. y == y .&. x

-- {-# ANN test (Theory Base.axioms) #-}
-- test :: Pantomime.BitVector 29 -> Bool
-- test x = x == complement (complement x)

add :: Maybe Int -> ( Maybe Int , Maybe Int ) -> ( Maybe Int , Maybe Int )
add _ ( Just 0 , Just b) = ( Nothing , Just b)
add _ ( Just a , Just b) = ( Just (a+b) , Nothing )
add s _ = ( Nothing , s)

-- {-# ANN test (Theory Base.axioms) #-}
test :: Pantomime.BitVector 23 -> Bool
test x = x == Pantomime.stupidMinBound
-- test :: Maybe Int -> (Maybe Int, Maybe Int) -> (Maybe Int, Bool)
-- test s i = let (s', o) = add s i in (s', isJust o)

-- test :: [Int] -> Bool
-- test xs = all (>= 0) $ take' 2 xs
-- test xs
--   | length' xs' == 50 = all (>= 0) xs'
--   | otherwise = True
--   where
--     xs' = take' 50 xs
-- test xs = or $ repeat True
-- test xs = or $ drop 1 xs

length' :: [a] -> Int
length' [] = 0
length' (_ : xs) = 1 + length' xs

take' :: Int -> [a] -> [a]
take' n xs = if
  | 0 < n -> unsafeTake n xs
  | otherwise -> []
  where
    unsafeTake = \cases
      !_ [] -> []
      1 (y:_) -> [y]
      m (y:ys) -> y : unsafeTake (m - 1) ys

-- or' :: [Bool] -> Bool 
-- or' = \case
--   [] -> False
--   x : xs -> x || False
-- test xs = case drop 1 xs of
--   [_] -> True
--   _ -> False

-- test :: Signed 1 -> Signed 2 -> Bool
-- test x _y = do
-- -- test x y = x .&. y == y .&. x
-- -- test :: Signed (4 + 1) -> Unsigned 2 -> Bool
-- -- test :: Signed 5 -> Unsigned 2 -> Bool
-- -- test x y = do
-- --   let x' = bitCoerce x
--   0 <= x

type family BitSz x :: Nat

type instance BitSz (Pantomime.BitVector n) = n

-- test :: Pantomime.BitVector (BitSz (Pantomime.BitVector 2)) -> Bool
-- test x = go @(Pantomime.BitVector 2) x
--   where
--     go :: forall bv. Pantomime.BitVector (BitSz bv) -> Bool
--     go y = y == y

-- type family TestFam x

-- type instance TestFam Bool = Int

-- test :: Pantomime.BitVector (BitSz (Pantomime.BitVector 2)) -> Bool
-- test x = go @(Pantomime.BitVector 2) x
--   where
--     go :: forall bv. Pantomime.BitVector (BitSz bv) -> Bool
--     go y = y == y

-- test :: TestFam Bool -> Bool
-- test x = go @Bool (x, x)
--   where
--     go :: forall a. Eq (TestFam a) => (TestFam a, Int) -> Bool
--     go v = v == v


-- test :: Int -> Bool
-- test _ = raise# ()
-- test :: BitVector 5 -> BitVector 2 -> Bool
-- test x _y = do
--   -- let x' = bitCoerce x
--   -- let x' = resize @_ @_ @3 x ++# resize @_ @_ @2 x
--   msb x == msb x
  -- resize x == y
  -- slice d3 d2 x == y

-- test :: Signed 5 -> Bool
-- test x = do
--   let y = unsafeCoerce $ x + 1
--   unsafeCoerce y == x
  -- let x' = bitCoerce x
  -- resize x == x
  -- x == bitCoerce y

-- {-# ANN test (Theory mempty) #-}
-- test :: BitVector (3 + 4) -> BitVector (6 + 9) -> Bool
-- test x y = do
--   let z = shiftL x 1
--   BitVector.select @1 @2 x == BitVector.select @2 @2 z

-- test :: WordN (3 + 2) -> IntN 5 -> Bool
-- test x y = do
--   -- let b = 0 :: IntN 1
--   -- let z = sizedBVConcat (sizedBVSelect @_ @2 @1 x) (sizedBVSelect @_ @1 @1 x) 
--   let z = shiftL x 1
--   sizedBVSelect @_ @1 @2 x == sizedBVSelect @_ @2 @2 z
  -- sizedBVConcat b x == sizedBVConcat b x
-- test :: Int -> Bool
-- test x = x + 1 == 0

-- test :: IntN 5 -> IntN 5 -> Bool
-- test x y = (x ++# y) ==# (y ++# y)
-- test x y = eqIntN x x

-- newtype Signed' n = Signed' (IntN n)

-- {-# OPAQUE (++#) #-}
-- (++#) :: forall n. KnownNat n => Signed' n -> Signed' n -> Signed' n
-- (++#) = coerce plusIntN

-- {-# OPAQUE (==#) #-}
-- (==#) :: forall n. KnownNat n => Signed' n -> Signed' n -> Bool
-- (==#) = coerce eqIntN

-- {-# ANN test (TestAnnot (+1)) #-}
-- {-# ANN test (SymCompare 'test) #-}
-- test :: Int8 -> Int8
-- test = (+ I8# 300#Int8)

-- data IntN (n :: Nat)

-- instance Num (IntN n) where
--   {-# OPAQUE (+) #-}
--   (+) = undefined
--   (*) = undefined
--   abs = undefined
--   signum = undefined
--   fromInteger = undefined
--   negate = undefined

-- {-# ANN test (SymCompare 'test) #-}
-- test :: IntN 32 -> IntN 32 -> IntN 32
-- test = plusIntN
-- test = (+)

-- {-# ANN test (SymCompare 'test) #-}
-- -- test :: Integer
-- -- test = 300000000000000000000000
-- test :: Int -> Word
-- test idx = shiftL 5 idx
-- {-# ANN test Theory #-}
-- test :: Int -> Bool
-- test x = x == x * 2

-- {-# ANN test (SymCompare 'test) #-}
-- -- test :: Int8# -> Int8#
-- -- test x = plusInt8# x 1#Int8

-- -- test :: Int -> Int
-- -- test x = case x > I# 5# of
-- --   True -> x + I# 25#
-- --   False -> x * I# 2#

-- test :: Int -> Bool
-- test x = x > I# 5#

-- {-# ANN test (SymCompare 'test) #-}
-- test :: Bool -> Bool
-- test = wow
-- test :: Bool -> Bool -> Bool
-- test _x = test1

-- test1 :: Bool -> Bool
-- test1 = \case
--   True -> False
--   False -> True

-- data Test where
--   X :: Test
--   Y :: a -> Test

-- test :: (Bool, Bool) -> (Test, Test)
-- test = \case
--   (True, False) -> (X, Y ()) 
--   (False, True) -> (X, Y True)
--   (_, _) -> (X, Y False)
  
-- test :: Int8# -> Int8
-- test _ = 1
  -- Y _ -> I8# 1#Int8
-- test :: Int -> Int
-- -- test x = (x + 1) * 5
-- test x = case x > 5 of
--   True -> 4 + x
--   False -> 5 + x

-- {-# ANN #-}

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: (# Int, Int #) -> (# Int, Int #)
-- test (# x, y #) = (# y, x #)

-- test2 :: (# Int, Int #) -> (# Int, Int #)
-- test2 (# x, _ #) = (# x, x #)

-- gaba :: Int
-- gaba = I# $ raise# ()


-- waba :: Int#
-- waba = raiseOverflow# (# #)

-- test2 :: Int -> Int
-- test2 = id

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Int -> Int
-- test = (+1)

-- test2 :: Int -> Int
-- test2 = id

-- {-# ANN test (SymCompare 'test) #-}
-- test :: BitVector 32 -> (BitVector 16, BitVector 16)
-- test = split

-- {-# ANN test (SymCompare 'test) #-}
-- test :: BitVector 32
-- test = 0

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Unsigned 32 -> BitVector 32
-- test = pack

-- test2 :: Unsigned 32 -> BitVector 32
-- test2 = (+ 1) . pack

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Unsigned 21 -> Unsigned 21 -> Unsigned 21
-- test x y = x + y

-- test2 :: Unsigned 21 -> Unsigned 21 -> Unsigned 21
-- test2 x y = x + y - 15

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Unsigned 0 -> Unsigned 0 -> Unsigned 0
-- test x y = x + y

-- test2 :: Unsigned 0 -> Unsigned 0 -> Unsigned 0
-- test2 x y = x + y - 15

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Signed 32 -> BitVector 32
-- test = pack

-- test2 :: Signed 32 -> BitVector 32
-- test2 = pack . (+ 2)

-- {-# ANN test (SymCompare 'test) #-}
-- test :: BitVector (1 + 15) -> BitVector 16
-- test = (+ 1)

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Unsigned 32 -> Unsigned 32
-- test x = shiftR x 8

-- test2 :: Unsigned 32 -> Unsigned 32
-- test2 x = shiftR x 4

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 64 -> (Integer, Bool)
-- test x = do
--   let y = toInteger# x
--   (y, x /= 0)

-- test2 :: BitVector 64 -> (Integer, Bool)
-- test2 x = do
--   let y = toInteger# x
--   (y, x == 0)

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 32 -> Unsigned 32
-- test = unpack

-- test2 :: BitVector 32 -> Unsigned 32
-- test2 = unpack . (+ 2)

-- {-# ANN test (SymCompare 'test) #-}
-- test :: BitVector 16 -> BitVector 16
-- test = complement

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 1 -> BitVector 1
-- test = (+ negate 1)

-- test2 :: BitVector 1 -> BitVector 1
-- test2 = id

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 0 -> BitVector 0
-- test = (+ negate 1)

-- test2 :: BitVector 0 -> BitVector 0
-- test2 = id

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 1 -> Int
-- test = size#

-- test2 :: BitVector 1 -> Int
-- test2 _ = 1

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 10 -> BitVector 6 -> BitVector 16
-- test = (++#)

-- test2 :: BitVector 10 -> BitVector 6 -> BitVector 16
-- test2 = flip (++#)

-- type role MyBitVec nominal

-- data MyBitVec (n :: Natural) where
--   MyBitVec :: Int -> MyBitVec n

-- class MyBitPack a where
--   type MyBitSize a :: Natural

--   mypack :: a -> MyBitVec (MyBitSize a)
-- -- type family MyBitSize n :: Natural

-- -- type instance MyBitSize (MyBitVec n) = n
-- instance MyBitPack (MyBitVec n) where
--   type MyBitSize (MyBitVec n) = n

--   mypack = id

-- mymsb' :: MyBitVec n -> Int
-- mymsb' (MyBitVec n) = n

-- mymsb :: MyBitPack a => a -> Int
-- mymsb x = mymsb' (mypack x)

-- -- incbv :: MyBitVec n -> MyBitVec n
-- -- incbv (MyBitVec x) = MyBitVec x

-- -- {-# ANN test (SymCompare 'test) #-}
-- test :: MyBitVec 32 -> Int
-- test = mymsb

-- type family MyBitSize n = n where
--   WordBits (MyBitVec n) = 32
--   WordBits PW8 = 64
-- type family MyBitSize n where
-- instance MyBitSize (MyBitVec n) = n

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 32 -> Bit
-- test = msb
-- -- test v = msb# (pack v)

-- test2 :: BitVector 32 -> Bit
-- -- test2 v = msb# (pack v)
-- test2 _ = high

-- test2 :: Bit -> Bit -> Bool
-- test2 = (/=)

-- test2 :: BitVector 16 -> BitVector 8
-- test2 = slice d14 d7

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 16 -> BitVector 1
-- test = slice d0 d0

-- test2 :: BitVector 16 -> BitVector 1
-- test2 = slice d1 d1

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 16 -> BitVector 8
-- test = slice d8 d1

-- test2 :: BitVector 16 -> BitVector 8
-- test2 = slice d7 d0

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: BitVector 16 -> BitVector 1
-- test = slice d1 d1

-- test2 :: BitVector 16 -> BitVector 1
-- test2 = slice d2 d2

-- data MyRecord = MyRecord
--   { field1 :: Int
--   , field2 :: Int -> Int
--   }

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Int -> MyRecord
-- test x = MyRecord
--   { field1 = x
--   , field2 = (x+)
--   }

-- test2 :: Int -> MyRecord
-- test2 x = MyRecord
--   { field1 = x
--   , field2 = (x+)
--   }

-- data MyRecord = MyRecord
--   { field1 :: Int -> Int
--   }

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Int -> Int -> MyRecord
-- test x y = MyRecord
--   { field1 = (x+y+)
--   }

-- test2 :: Int -> Int -> MyRecord
-- test2 x y = MyRecord
--   { field1 = (x+y+1+)
--   }

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: (Int# -> Int) -> Int
-- test f = f 4#

-- test2 :: (Int# -> Int) -> Int
-- test2 f = f 4#

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Int -> Int
-- test x = shiftR x 8

-- test2 :: Int -> Int
-- test2 x = shiftR x 8

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: MyRecord
-- test = MyRecord
--   { field1 = (\v -> I# (1# +# v))
--   }

-- test2 :: MyRecord
-- test2 = MyRecord
--   { field1 = (\v -> I# (2# +# v))
--   }

-- -- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int64# -> Int64#
-- test2 x = let z = plusInt64# x 5#Int64 in z

-- {-# ANN test UCSymbolic #-}
-- test :: Int64# -> Int64#
-- test x = let z = plusInt64# x (intToInt64# 5#) in z

-- {-# ANN test UCSymbolic #-}
-- test :: Int# -> Int#
-- test x = let z = uncheckedIShiftRA# x 5# in (\y -> y +# 1#) z

-- {-# ANN test UCSymbolic #-}
-- test :: Int# -> Int#
-- test x = f (x -# 5#) +# f x 
--   where
--     f y = x +# y

-- {-# ANN test UCSymbolic #-}
-- test :: Int# -> Int#
-- test x = h f (x -# 5#) +# h f x 
--   where
--     f y = x +# y
--     h g y = g x +# y

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int64# -> Int64#
-- test2 x = case x of
--   20#Int64 -> 0x7b#Int64
--   _ -> 0#Int64

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int64# -> Int64#
-- test2 x = 
--   (case x of
--     20#Int64 -> \z -> plusInt64# 0x6b#Int64 z
--     _ -> \_ -> 0#Int64)
--   (case x of
--     19#Int64 -> 0x5#Int64
--     _ -> 0x10#Int64)

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int64# -> Int64# -> Int64#
-- test2 lhs rhs = case lhs of
--   20#Int64 -> plusInt64# lhs 15#Int64
--   -- 15#Int64 -> plusInt64# lhs rhs
--   _ -> rhs

-- data MyRecord = MyRecord
--   { field0 :: Int
--   , field1 :: Int
--   }

-- {-# ANN test2 UCSymbolic #-}
-- -- test2 :: MyRecord -> Int
-- -- test2 record = field0 record + field1 record
-- test2 :: Int -> MyRecord
-- test2 val = MyRecord
--   { field0 = val
--   , field1 = val
--   }

-- data MyGADT a where
--   MyInt :: Int -> MyGADT Int
--   MyWord :: Word -> MyGADT Word

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: MyGADT a -> a
-- test2 = \case
--   MyInt x -> x
--   MyWord x -> x

-- newtype MyFun = MyFun (Int64 -> Int64)

-- data MyInfix where
--   (:--) :: Bool -> Bool -> MyInfix

-- {-# ANN test2 (SymCompare 'test3) #-}
-- test2 :: Bool -> Bool -> MyInfix
-- test2 x y = x :-- y

-- test3 :: Bool -> Bool -> MyInfix
-- test3 x y = y :-- x

-- data MyPair = MyPair
--   { field0 :: Int
--   , field1 :: Bool
--   }

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: MyPair -> MyPair
-- test pair = MyPair (field0 pair + 1) (field1 pair)

-- test2 :: MyPair -> MyPair
-- test2 pair = MyPair (field0 pair + 1) (field1 pair)

-- data MyPair = MyPair
--   { field0 :: Int
--   , field1 :: Bool
--   }

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Int# -> Int
-- test = I#

-- test2 :: Int# -> Int
-- test2 = I#

-- data MyEnum where
--   Value0 :: MyEnum
--   Value1 :: MyEnum

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: MyEnum
-- test = Value0

-- test2 :: MyEnum
-- test2 = Value1

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: MyFun -> Int64
-- test2 (MyFun f) = f 5

-- newtype MyInt64 = MyInt64 Int64
-- newtype MyInt64' = MyInt64' MyInt64
-- newtype MyInt64' = MyInt64' Int64

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int64 -> MyInt64'
-- test2 x = MyInt64' $ MyInt64 x
-- test2 :: MyInt64' -> Int64
-- test2 (MyInt64' (MyInt64 x)) = x
-- test2 (MyInt64 x) = MyInt64' x

-- {-# ANN test2 (SymCompare 'test3) #-}
-- test2 :: MyInt64 -> MyInt64'
-- test2 (MyInt64 x) = MyInt64' $ x + 1

-- test3 :: MyInt64 -> MyInt64'
-- test3 (MyInt64 x) = MyInt64' $ case x of
--   0x23 -> 0x7b
--   _ -> x + 1

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Int# -> Int#
-- test x = x +# 1#

-- test2 :: Int# -> Int#
-- test2 x = case x of
--   0x23# -> 0x7b#
--   _ -> x +# 1#

-- {-# ANN test2 (SymCompare 'test3) #-}
-- test2 :: (Bool, Int) -> (Int, Bool)
-- test2 (x, y) = (y, x)

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Int -> Bool -> (Bool, Bool)
-- test x y = (x == 0, y)

-- test2 :: Int -> Bool -> (Bool, Bool)
-- test2 x y = (x == 2, y)

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Either Int Word -> Either Int Word
-- test = \case
--   Right val -> Right 0
--   Left val -> Left val

-- test2 :: Either Int Word -> Either Int Word
-- test2 x = x

-- {-# ANN test (SymCompare 'test2) #-}
-- test :: Int -> Int
-- test x = x + 1

-- test2 :: Int -> Int
-- test2 x = case x of
--   0x23 -> 0x7b
--   _ -> x + 1

-- test2 :: Int -> Int
-- test2 x = case x of
--   20 -> 0x7b
--   _ -> x

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int64 -> Int64#
-- test2 x = case x of
--   I64# x' -> case x' of
--     0x20#Int64 -> 0x10#Int64
--     _ -> 0x15#Int64

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int64# -> Int64
-- test2 x = I64# x

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int64 -> Int64 -> (Int64, Int64)
-- test2 x y = (x, y)

-- {-# ANN test2 UCSymbolic #-}
-- test2 :: Int -> Int
-- test2 x = x + 1

-- test2 :: Int64# -> Int64#
-- test2 x = quotInt64# 30#Int64 x

-- {-# ANN test UCSymbolic #-}
-- test :: Int# -> Int#
-- test x = case x of
--   20# -> 0x7b#
--   _ -> 0#

-- test :: Int# -> Int#
-- test x = (case x of
--   20# -> \z -> 0x7b# +# z
--   _ -> \_ -> 0#)
--   0x10#

-- {-# ANN test UCSymbolic #-}
-- test :: Int64# -> Int64#
-- test x = let z = uncheckedIShiftL64# x 0x1# in z

-- data Strict a :: TYPE (BoxedRep Unlifted) where
--   Force :: !a -> Strict a

-- newtype Strict a :: TYPE (BoxedRep Unlifted) where
--   Force :: a -> Strict a

-- {-# ANN test UCNorm #-}
-- test :: Int -> Int -> Int
-- test x y = (4 + y) + x
-- test x y = (y + 4) + x
-- test x y = 4 + (y + x)
-- test x y = 4 + (x + y)
-- test x y = (x + y) + 4
-- test :: Int
-- test :: Int
-- test = fromInteger test'

-- test' :: Integer
-- test' = 4

-- data SMaybe a :: TYPE (BoxedRep Unlifted) where
--   SJust    :: !a -> SMaybe a
--   SNothing :: SMaybe a

-- {-# ANN test UCNorm #-}
-- test :: SMaybe Int -> Int
-- test x = case x of
--   SNothing -> 4
--   SJust _ -> 4

-- {-# ANN test UCNorm #-}
-- test :: Maybe Int -> Int
-- test x = case x of
--   Nothing -> 4
--   Just _ -> 4

-- {-# ANN test UCNorm #-}
-- test :: (Strict Int -> Strict Int) -> Strict Int -> Strict Int
-- test f (Force x) = f $ Force 0
-- test f (Force x) = f $ Force 0 case x of
--   0 -> Force 0
--   _ -> Force 2

-- test :: Int -> Int -> Int
-- test x y = case x of
--   0 -> 1
--   _ -> case y of
--     2 -> 3
--     _ -> case x of
--       4 -> 5
--       _ -> 6

-- test :: Maybe Int -> Bool
-- test s = s /= s


-- {-# ANN adder UC
--   { observation = 'obs
--   , leakage = 'leak
--   , simulator = 'sim
--   , projection = 'proj
--   } #-}
-- {-# ANN adder UCNorm #-}
-- adder :: Maybe Int -> Maybe (Int, Int) -> (Maybe Int, Maybe Int)
-- adder s i = case i of
--   Just (a, b) -> (Just $ a + b, s)
--   Nothing -> (Nothing, s)

-- -- {-# ANN compImpl UCNorm #-}
-- compImpl :: Maybe Int -> Maybe (Int, Int) -> (((), Maybe Ordering), Maybe Ordering)
-- compImpl = Projection.composeI adder obs proj

-- obs :: Num a => Ord a => Maybe a -> Maybe Ordering
-- obs (Just x) = Just $ compare x 0
-- obs _ = Nothing

-- leak :: Ord a => Num a => () -> Maybe (a, a) -> ((), Maybe Ordering)
-- leak _ (Just (x, y)) = ((), Just $ compare (x + y) 0)
-- leak _ _ = ((), Nothing)

-- sim :: Maybe Ordering -> Maybe Ordering -> (Maybe Ordering, Maybe Ordering)
-- sim s i = (i, s)

-- proj :: Num b => Ord b => Maybe b -> ((), Maybe Ordering)
-- proj = ((),) . obs

-- main :: IO ()
-- main = do
--   let val = 0x2aaaaaaaaaaaaac0#Word
--   let out = test (word2Int# val)
--   let word = int2Word# out
--   putStrLn $ showHex (W# word) ""

main :: IO ()
main = do
  -- let implobs s i = do
  --       let (s', o) = Core2.core s i
  --       (Core2.proj s', Core2.obs' o)

  -- let leaksim s i = do
  --       let (sl, ss) = Core2.proj s
  --       let (sl', l) = Core2.leak sl i
  --       let (ss', o) = Core2.sim ss l
  --       ((sl', ss'), o)

  let st = Core2.State
        { reg = 10
        , fePC = 1
        , exPC = 0
        , exInstr = Core2.Bz 8
        , wbRes = Just 0
        , wbOut = Nothing
        }
  let instr = 0x00ec

  let leaksim s i = do
        let (sl, ss) = Core2.proj s
        let (sl', x) = Core2.leak sl i
        let (ss', o) = Core2.sim ss x
        ((sl', ss'), o)
  let implobs s i = do
        let (s', o) = Core2.core s i
        (Core2.proj s', Core2.obs' o)

  print $ leaksim st instr
  print $ implobs st instr

  print $ Core2.theory st instr

  -- let st0 = Core2.State
  --       { reg = 0x00000000
  --       , fePC = 0xc1
  --       , exPC = 0x3d
  --       , exInstr = Core2.Bz 0x00
  --       , wbRes = Just 0x80000000
  --       , wbOut = Just 0x40000000
  --       }
  -- let instr0 = 0x0000

  -- let st1 = Core2.State
  --       { reg = 0x00000000
  --       , fePC = 0xc1
  --       , exPC = 0x3d
  --       , exInstr = Core2.Clr
  --       , wbRes = Just 0x00000000
  --       , wbOut = Just 0x00000000
  --       }
  -- let instr1 = 0x0000

  -- print $ Core2.theory1 st0 instr0 st1 instr1

  -- let leakproj s i = Core2.leak (fst $ Core2.proj s) i
  -- let implobs' s i = do
  --       let (s', o) = Core2.core s i
  --       (fst $ Core2.proj s', Core2.obs' o)

  -- print $ leakproj st0 instr0
  -- print $ leakproj st1 instr1

  -- print "=========="
  -- print $ leaksim st0 instr0
  -- print $ leaksim st1 instr1

  -- print "=========="
  -- print $ implobs' st0 instr0
  -- print $ implobs' st1 instr1

  -- print $ implobs st instr
  -- print $ leaksim st instr

  -- print $ Core2.theory st instr
-- main = runDiff

-- diff :: (State, Word16)
-- diff = (s, i)
--     where
--         s = State
--             { pc = 0
--             , reg = 0
--             , bubble = False
--             , nextPc = 0
--             , fetchPC = 0
--             , fetchInstruction = Beq 0
--             , writebackOut = (Just $ Write 10, Nothing)
--             }
--         i = 0xffff

-- main :: IO ()
-- main = do
--   let (s, i) = diff
--   let imp = Projection.composeI tickRun obs proj s i
--   let sim = Projection.composeS leakRun simRun proj s i
--   print $ snd imp
--   print $ snd sim
