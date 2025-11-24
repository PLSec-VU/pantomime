{-# LANGUAGE MagicHash #-}

module Core2
  ( Instr (..)
  , State (..)
  , core

  , LInstr (..)
  , LState (..)
  , leak_ex
  , leak_fe
  , leak

  , SState (..)
  , sim_ex
  , sim_fe
  , sim

  , proj
  , obs
  , obs'
  , theory
  -- , theory0
  -- , theory1
  ) where

import GHC.Word (Word8 (..), Word16 (..), Word32 (..))
import GHC.Base (wordToWord8#, word8ToWord#, word16ToWord#,  wordToWord32#)
import Data.Word
import Data.Bits
import Data.Maybe (fromMaybe)
import Pantomime (Pantomime(..), Theory (..), pantomime) --, NonInterference (..), nonInterference0, nonInterference1)
import Pantomime.Base qualified as Base
import Control.Arrow (Arrow(..))
import Data.Composition ((.:))

data Instr
  = Add Word8
  | Clr
  | Out
  | Jmp Word8
  | Bz Word8
  deriving (Eq, Show)

data State = State
  { reg :: Word32 
  , fePC :: Word8 
  , exPC :: Word8 
  , exInstr :: Instr 
  , wbRes :: Maybe Word32
  , wbOut :: Maybe Word32
  }
  deriving (Eq, Show)

fetch :: State -> (Word16, Maybe Word8) -> State
fetch state@State { fePC } (rawInstr, jump) = do
  let (exInstr, fePC') = case jump of 
        Just jmpPC -> (Add 0, jmpPC) -- Add 0 == no-op
        Nothing -> (decode rawInstr, fePC + 1)
  state { exPC = fePC , exInstr, fePC = fePC' }

execute :: State -> (State, Maybe Word8)
execute state@State { exInstr, reg, exPC } = do
  let wbRes = case exInstr of
        Add imm -> Just (reg + word8ToWord32 imm)
        Clr -> Just 0
        _ -> Nothing
  let wbOut = case exInstr of
        Out -> Just reg
        _ -> Nothing
  let jump = case exInstr of
        Bz off | reg == 0 -> Just (exPC + off)
        Jmp addr -> Just addr
        _ -> Nothing
  (state { wbRes, wbOut }, jump)

writeback :: State -> (State, Maybe Word32)
writeback state@State { reg, wbRes, wbOut } = do
  let reg' = case wbRes of Just value -> value; Nothing -> reg
  (state { reg = reg' }, wbOut)

core :: State -> Word16 -> (State, (Maybe Word32, Word8))
core state0 rawInstr = do
  let (state1, out) = writeback state0
  let (state2, jump) = execute state1
  let state3  = fetch state2 (rawInstr, jump)
  (state3, (out, fePC state3))

{-# ANN theory (Theory Base.axioms) #-}
theory :: State -> Word16 -> Bool
theory = pantomime Pantomime
  { implementation = core
  , leakage = leak
  , simulator = sim
  , observation = obs'
  , projection = proj
  }

-- -- {-# ANN theory0 (Theory Base.axioms) #-}
-- theory0 :: State -> Word16 -> Bool
-- theory0 = nonInterference0 whole

-- -- {-# ANN theory1 (Theory Base.axioms) #-}
-- theory1 :: State -> Word16 -> State -> Word16 -> Bool
-- theory1 = nonInterference1 whole

-- whole :: NonInterference State LState SState Word16 LInstr Word8
-- whole = NonInterference
--   { implementation = second obs' .: core
--   , leakage = leak
--   , projection = proj
--   }

-- data NonInterference si sl ss i l o where
--   NonInterference ::
--     { implementation :: Circuit si i o
--     , leakage :: Circuit sl i l
--     , projection :: si -> (sl, ss)
--     } -> NonInterference si sl ss i l o

-- nonInterference0
--   :: Eq sl
--   => NonInterference si sl ss i l o
--   -> si
--   -> i
--   -> Bool
-- nonInterference0 NonInterference { .. } = do
--   let leakage' s i = do
--         let (sl, _ss) = projection s
--         let (sl', _o) = leakage sl i
--         sl'
--   let implementation' s i = do
--         let (s', _o) = implementation s i
--         let (sl', _ss') = projection s'
--         sl'

--   \s i -> leakage' s i == implementation' s i

-- nonInterference1
--   :: Eq o
--   => Eq l
--   => Eq ss
--   => NonInterference si sl ss i l o
--   -> si
--   -> i
--   -> si
--   -> i
--   -> Bool
-- nonInterference1 NonInterference { .. } = do
--   let leakage' s i = do
--         let (sl, ss) = projection s
--         let (_sl', o) = leakage sl i
--         (ss, o)
--   let implementation' s i = do
--         let (s', o) = implementation s i
--         let (_sl', ss') = projection s'
--         (ss', o)

--   \s i s' i' -> do
--     (leakage' s i == leakage' s' i') `implies` (implementation' s i == implementation' s' i')

-- whole :: NonInterference State LState Word16 LInstr Word8
-- whole = NonInterference
--   { implementation = second obs' .: core
--   , leakage = leak
--   , projection = fst . proj
--   }

-- data NonInterference si sl i l o where
--   NonInterference ::
--     { implementation :: Circuit si i o
--     , leakage :: Circuit sl i l
--     , projection :: si -> sl
--     } -> NonInterference si sl i l o

-- nonInterference0
--   :: Eq sl
--   => NonInterference si sl i l o
--   -> si
--   -> i
--   -> Bool
-- nonInterference0 NonInterference { .. } = do
--   let leakage' s i = fst $ leakage (projection s) i
--   let implementation' s i = projection . fst $ implementation s i

--   \s i -> leakage' s i == implementation' s i

-- nonInterference1
--   :: Eq si
--   => Eq sl
--   => Eq l
--   => Eq o
--   => NonInterference si sl i l o
--   -> si
--   -> i
--   -> si
--   -> i
--   -> Bool
-- nonInterference1 NonInterference { .. } = do
-- --   let leakage' s i = do
-- --         let (sl, ss) = projection s
-- --         let (_sl', o) = leakage sl i
-- --         (ss, o)
-- --   let implementation' s i = do
-- --         let (s', o) = implementation s i
-- --         let (_sl', ss') = projection s'
-- --         (ss', o)
--   let leakage' s i = snd $ leakage (projection s) i
--   let implementation' s i = snd $ implementation s i
--   \s i s' i' -> do
--     (leakage' s i == leakage' s' i') `implies` (implementation' s i == implementation' s' i')
  -- undefined



-- data NonInterference si sl i l o where
--   NonInterference ::
--     { implementation :: Circuit si i o
--     , leakage :: Circuit sl i l
--     , projection :: si -> sl
--     } -> NonInterference si sl i l o

-- nonInterference
--   :: Eq o
--   => Eq l
--   => NonInterference si sl i l o
--   -> si
--   -> i
--   -> si
--   -> i
--   -> Bool
-- nonInterference NonInterference { .. } = do
--   let leakage' s i = snd $ leakage (projection s) i
--   let implementation' s i = snd $ implementation s i

--   \s i s' i' -> do
--     (leakage' s i == leakage' s' i') `implies` (implementation' s i == implementation' s' i')

--   let leakproj s i = snd $ leakage (projection s) i
--   let implobs (si, so) i = do
--         let (_si', o) = implementation si i
--         let (_so', o') = observation so o
--         o'

--   let implies x y = not x || y

--   \s i s' i' -> do
--     (leakproj s i == leakproj s' i') `implies` (implobs s i == implobs s' i')
  -- undefined
  -- let leak' s i = leakage (fst $ projection s) i
  -- let impl' = bimap projection observation .: implementation
  -- let test = first snd .: impl'

  -- let implies x y = not x || y
  -- \s i s' i' -> do
  --   let pre = leak' s i == leak' s' i'
  --   let post = test s i == test s' i'
  --   pre `implies` post
    -- fst (big s i) == fst (small s i)
  -- undefined
  -- \si i -> chkState si i == chkState si i

  -- let chkState s i = fst (big s i) == fst (small s i)
  -- \si i -> chkState si i == chkState si i
  


-- theory' :: State -> Word16 -> Bool
-- theory' = do
--   let leakproj s i = first proj $
--   -- let implProjState
--   -- let eq =
--   undefined

-- impl-proj-state : S → Iℓ → Sℓ
--   impl-proj-state s i =
--     let (s' , o) = impl s i
--          sℓ = proj s'
--     in sℓ
--   leak-proj-state : S → Iℓ → Sℓ
--   leak-proj-state s i =
--     let sℓ = proj s
--          (sℓ' , _) = leak sℓ i
--     in sℓ'
--   impl-obs-proj-so : S ⊗ Iℓ → Oₛ
--   impl-obs-proj-so (s, i) =
--     let (s' , o) = impl s i
--     in o
--   leak-proj-so : S ⊗ Iℓ → Oℓ
--   leak-proj-so (s, i) =
--     let sℓ = proj s
--         (sℓ' , o) = leak sℓ i
--     in o
-- LeakStateConsistency : Type
--   LeakStateConsistency = ∀ s i
--     → impl-proj-state s i ≡ leak-proj-state s i
--   LeakOutputConsistency : Type
--   LeakOutputConsistency = ∀ si si'
--     → leak-proj-so si ≡ leak-proj-so si'
--     → impl-obs-proj-so si ≡ impl-obs-proj-so si'

------------------------------------
-- | TEST
------------------------------------

-- procStart
--   :: Circuit
--     (State, ())
--     Word16
--     Word8
-- procStart (si, so) i = do
--   let (si', po) = proc si i
--   let (so', oo) = obs so po
--   ((si', so'), oo)

proj :: State -> (LState, SState)
proj State { reg, exInstr, fePC, exPC, wbRes } = do
  -- let lreg = fromMaybe reg wbRes
  -- (LState { lreg = reg, lexInstr = exInstr, lwbRes = wbRes }, SState { sfePC = fePC, sexPC = exPC })
  (LState { lreg = reg, lexInstr = exInstr, lwbRes = wbRes }, SState { sfePC = fePC, sexPC = exPC })
  -- (LState { reg, exInstr }, SState { fePC, exPC })
-- proj (state, _) = do
--   let lstate = LState
--         { lreg = reg state
--         , lexInstr = exInstr state
--         }

--   let sstate = SState
--         { sfePC = fePC state
--         , sexPC = exPC state
--         }

--   (lstate, sstate)

-- TODO: I'm not actually sure about this.
-- We really cannot treat all the intermediate stages as statefull circuits.
-- More accurate would be to see them as pure functions that map both some value
-- named state and some other values. In no way will the state actually be
-- looped as is.
--
-- I think the top level goal we have is accurate, but as something for the
-- looped proc. How about an intermediate observation for the non loopied
-- version. My intuition says that we only care about the program counter and
-- we can even get away with not observing the State.
--
-- Then the question is, what is the final goal?
--
-- I guess at the end we want a leakage and simulator circuit. That is, actual
-- loopy circuits that each have their own state and are simply sequentially
-- composed.
--
-- How would we construct this out of our linear leakage and simulator?
-- I guess the linear leakage and simulator should have a particular shape no?
--
-- Hmm. Actually, it is exactly dictated by the outer shell. Namely, we should
-- create a projection function for the inner one.

-- feGoal :: State -> (Word16 , Maybe Word8) -> (State, ())
-- feGoal _ _ = undefined

------------------------------------
-- | Modular leakage and simulator
------------------------------------

data LInstr
  = LJmp Word8
  | LBr Word8
  | LOther
  deriving (Eq, Show)

data LState = LState
  { lreg :: Word32
  , lexInstr :: Instr
  , lwbRes :: Maybe Word32
  }
  deriving (Eq, Show)

leak_ex :: LState -> (LState , (LInstr, Bool))
leak_ex state = do
  let curReg = lreg state
  case lexInstr state of
    Add imm -> let newReg = curReg + word8ToWord32 imm in 
      (state {lreg = newReg}, (LOther, False))
    Clr -> 
      (state {lreg = 0}, (LOther, False))
    Out -> 
      (state, (LOther, False))
    Jmp addr ->
      (state,  (LJmp addr, True))
    Bz off ->
      if curReg == 0
      then ( state, (LBr off, True))
      else ( state, (LOther, False))   

sim_ex :: () -> LInstr -> ((), (Instr, Bool))
sim_ex _ lInst = 
  case lInst of
    LJmp addr ->
      ((), (Jmp addr, True))
    LBr off ->
      ((), (Bz off, True))
    LOther ->
      ((), (Add 0, False))

leak_fe :: LState -> (Word16, Bool) -> (LState , ())
leak_fe state (rawInstr, jmp) = do
  let instr = decode rawInstr
  let instr' = if
        | jmp -> instr
        | otherwise -> Add 0

  (state { lexInstr = instr' }, ())

sim_fe :: SState -> (Instr, Bool) -> (SState, Word8)
sim_fe state (instr, jmp) = do
  let curPC = sfePC state
  case instr of
    Jmp addr -> (state { sexPC = curPC , sfePC = addr }, addr)
    Bz off | jmp -> do
      let newPC = sexPC state + off
      (state { sexPC = curPC , sfePC = newPC }, newPC)
    _ -> (state { sexPC = curPC , sfePC = curPC + 1}, curPC + 1)

-----------------------------
-- | Monolithic Leakage
-----------------------------
leak :: LState -> Word16 -> (LState, LInstr)
leak LState { lreg, lexInstr, lwbRes } rawInstr = do
  let lreg' = case lwbRes of Just value -> value; Nothing -> lreg
  let lwbRes' = case lexInstr of
        Add imm -> Just (lreg' + word8ToWord32 imm)
        Clr -> Just 0
        _ -> Nothing
  let (lexInstr', leakInstr) = case lexInstr of
        Jmp addr -> (Add 0, LJmp addr)
        -- Bz off | lreg' == 0 -> (Add 0, LBr off)
        Bz off | lreg == 0 -> (Add 0, LBr off)
        _ -> (decode rawInstr, LOther)
  (LState { lreg = lreg', lexInstr = lexInstr', lwbRes = lwbRes' }, leakInstr)

data SState = SState
  { sfePC :: Word8
  , sexPC :: Word8
  }
  deriving (Eq, Show)

sim :: SState -> LInstr -> (SState, Word8)
sim state@SState { sfePC, sexPC } leakInstr = do
  let sfePC' = case leakInstr of
        LJmp addr -> addr
        LBr off -> sexPC + off
        LOther -> sfePC + 1
  (state { sexPC = sfePC, sfePC = sfePC' }, sfePC')

obs :: () -> (Maybe Word32, Word8) -> ((), Word8)
obs = stateless obs'

obs' :: (Maybe Word32, Word8) -> Word8
obs' = snd

stateless :: (a -> b) -> () -> a -> ((), b)
stateless f _ x = ((), f x)

-----------------------------
-- | Encoding and decoding
-----------------------------

-- word8ToWord16 :: Word8 -> Word16
-- word8ToWord16 (W8# value) = W16# $ wordToWord16# (word8ToWord# value)

word8ToWord32 :: Word8 -> Word32
word8ToWord32 (W8# value) = W32# $ wordToWord32# (word8ToWord# value)

word16ToWord8 :: Word16 -> Word8
word16ToWord8 (W16# value) = W8# $ wordToWord8# (word16ToWord# value)

-- encode :: Instr -> Word16
-- encode instruction = case instruction of
--     Add value -> (0 `shiftL` 8) .|. word8ToWord16 value
--     Clr       -> 1 `shiftL` 8
--     Out       -> 2 `shiftL` 8
--     Jmp addr    -> (3 `shiftL` 8) .|. word8ToWord16 addr
--     Beq off   -> (4 `shiftL` 8) .|. word8ToWord16 off

decode :: Word16 -> Instr
decode word = case shiftR word 8 of
    0 -> Add (word16ToWord8 (word .&. 0xFF))
    1 -> Clr
    2 -> Out
    3 -> Jmp (word16ToWord8 (word .&. 0xFF))
    4 -> Bz (word16ToWord8 (word .&. 0xFF))
    _ -> Add 0
    --_ -> error "Invalid instruction"
