{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-all #-}

module ProcessorControlModular
    ( test
    , tickRun
    , obs
    , leakRun
    , simRun
    , proj
    ) where

import GHC.Base (wordToWord8#, word8ToWord#, word16ToWord#, wordToWord16#, wordToWord32#)
import GHC.Word (Word8 (..), Word16 (..), Word32 (..))
import Data.Word
import Data.Bits
import Control.Monad.State (MonadState, MonadIO, put, get, runStateT, runState, liftIO)
import Data.Maybe (isJust)
import Data.Tuple (swap)
import Projection
import UC
import Test.QuickCheck hiding ((.&.))
import Debug.Trace

data Instruction = Add Word8
                -- ^ Add immediate to the register
                |  Clr
                -- ^ Reset the register to zero
                |  Out 
                -- ^ Output the register value
                | J Word8        
                -- ^ Jump to target address
                | Beq Word8      
                -- ^ Branch if register equals zero to PC + offset
                deriving (Eq, Ord, Show) 

-- 16-bit word layout:
-- +--------+--------+
-- | Opcode | Value  |
-- +--------+--------+
-- 15      8 7      0
--
-- Opcode:
-- 00 - Add (with 8-bit immediate value)
-- 01 - Clr
-- 10 - Out
-- 11 - J (with 8-bit target address)
-- 100 - Beq (with 8-bit offset)

word8ToWord16 :: Word8 -> Word16
word8ToWord16 (W8# value) = W16# $ wordToWord16# (word8ToWord# value)

word8ToWord32 :: Word8 -> Word32
word8ToWord32 (W8# value) = W32# $ wordToWord32# (word8ToWord# value)

word16ToWord8 :: Word16 -> Word8
word16ToWord8 (W16# value) = W8# $ wordToWord8# (word16ToWord# value)

encode :: Instruction -> Word16
encode instruction = case instruction of
    Add value -> (0 `shiftL` 8) .|. word8ToWord16 value
    Clr       -> 1 `shiftL` 8
    Out       -> 2 `shiftL` 8
    J addr    -> (3 `shiftL` 8) .|. word8ToWord16 addr
    Beq off   -> (4 `shiftL` 8) .|. word8ToWord16 off

decode :: Word16 -> Instruction
decode word = case shiftR word 8 of
    0 -> Add (word16ToWord8 (word .&. 0xFF))
    1 -> Clr
    2 -> Out
    3 -> J (word16ToWord8 (word .&. 0xFF))
    4 -> Beq (word16ToWord8 (word .&. 0xFF))
    _ -> Add 0
    --_ -> error "Invalid instruction"

testEncoding :: IO ()
testEncoding = do
    let testInsts = [Add 42, Clr, Out, J 10, Beq 5]
    let results = map (\inst -> decode (encode inst) == inst) testInsts
    putStrLn $ "Encode/decode tests passed: " ++ show (and results)
    putStrLn $ "Individual results: " ++ show (zip testInsts results)

data State = State {
    -- architectural state
    pc :: Word8,
    reg :: Word32,
    -- pipeline registers
    fetchPC :: Word8,
    fetchInstruction :: Instruction,
    writebackOut :: (Maybe Writeback, Maybe Output)
} deriving (Eq, Show)

-- Helper types remain the same
newtype Output = Val Word32 deriving (Eq, Show)
newtype Writeback = Write Word32 deriving (Eq, Show)

-- -- | Pipeline Stages
fetch :: MonadState State m => Word8 -> Word8 -> Bool -> Word16 -> Maybe Output -> m (Word8, Instruction, Word8, Maybe Output)
fetch pc nextPc bubble rawInstr out = do
    --(pc, fetchInstruction, fetchPC, out)
    let inst = if bubble 
               then Add 0  -- No-op
               else decode rawInstr
    pure $ (nextPc, inst, pc, out)

execute :: MonadState State m => Word32 -> Word16 -> Maybe Output -> Word8 -> Instruction -> Word8 -> m ((Maybe Writeback, Maybe Output), Word8, Word8, Bool, Word16, Maybe Output)
execute reg rawInst out pc inst fetchPc = do 
    case inst of
        Add value -> 
            let result = reg + fromIntegral value in
            return ((Just $ Write result, Nothing), pc, pc+1, False, rawInst, out)
        Clr ->
            return ((Just (Write 0), Nothing), pc, pc+1, False, rawInst, out)
        Out ->
            return ((Nothing, Just $ Val reg), pc, pc+1, False, rawInst, out)
        J addr ->
            return ((Nothing, Nothing), pc, addr, True, rawInst, out)
        Beq offset ->
            if reg == 0 
            then pure ((Nothing, Nothing), pc, fetchPc + offset, True, rawInst, out) 
            else pure ((Nothing, Nothing), pc, pc + 1, False, rawInst, out)

writeback :: MonadState State m => (Maybe Writeback, Maybe Output) -> Word16 -> Word32 -> m (Word32, Word16, Maybe Output)
writeback wbOut rawInst reg = do
   let (wb, out) = wbOut
   -- Update register if there's a writeback
   let newReg = maybe reg (\(Write v) -> v) wb
   return (newReg, rawInst, out)

tick :: MonadState State m => Word16 -> m (Maybe Output, Word8)
tick rawInst = do
   state <- get
   -- writeback
   (newReg, rawInst, out) <- writeback (writebackOut state) rawInst (reg state) -- wbOut rawInst reg
   put $ state {reg = newReg}
   -- execute
   -- Word32 -> Word16 -> Maybe Output -> Word8 -> Instruction -> Word8 -> m ((Maybe Writeback, Maybe Output), Word8, Word8, Bool, Word16, Maybe Output)
   state <- get
   (wbOut, newPc, nextPc, bubble, rawInst, out) <- execute (reg state) rawInst out (pc state) (fetchInstruction state) (fetchPC state)
   put $ state {writebackOut = wbOut}
   -- fetch
   state <- get
   (newPc, fetchInst, newFetchPC, out) <- fetch newPc nextPc bubble rawInst out
   put $ state {pc = newPc, fetchInstruction=fetchInst,  fetchPC=newFetchPC}
   return (out, newPc)

tickRun :: State -> Word16 -> (State, (Maybe Output, Word8))
tickRun s i = swap $ runState (tick i) s    

initState = State { 
       pc = 0, 
       reg = 0, 
       fetchInstruction = Add 0,
       writebackOut = (Nothing, Nothing)
   }

run :: MonadState State m => Int -> [Word16] -> m [Word8]
run maxSteps program = go maxSteps
  where
    go steps = do
      state <- get
      if steps <= 0
      then return []  -- Terminate if max steps reached
      else if pc state >= fromIntegral (length program)
      then return []  -- Terminate if program complete
      else do
        let inst = program !! fromIntegral (pc state)
        (out, pc) <- tick inst
        os <- go (steps - 1)  -- Decrement remaining steps
        return $ pc:os

test :: IO ()
test = do
    putStrLn "Test 1: Jump"
    runAndShow run prog initState
 where
   maxSteps = 50
   prog = [Out, Add 228, J 8, Add 11, Clr, Clr, Add 53, J 2, Beq 0, Out, Clr, Out, Out, Add 190, Beq 5, J 9, Add 155]
   prog1 = [Out, J 3, Add 5, Add 10, Out, Out, Out, Out]  -- Should output 0, 10, 10
   prog2 = [Add 1, Out, Clr, Out, Beq 2, Out, Add 2, Out, Out, Out, Out]  -- Should output 1, 1, 3

   runAndShow runF prog init = do
       (outs, s) <- runStateT (runF maxSteps $ map encode prog) init
       putStrLn $ "State: " ++ show s
       putStrLn $ "Outputs: " ++ show outs


------------------------------------------------------------------------------------
-- Leakage Description and Proof
------------------------------------------------------------------------------------

-- | Instructions passed to the Simulator
data LeakInst = LBeq Word8
-- ^ are we taking the branch + offset
            | LJ Word8
-- ^ jump target                
            | LOther 
-- ^ all other instructions
    deriving (Eq, Ord, Show) 

-- | Attacker can only see the PC.
obs :: (Maybe Output, Word8) -> Word8
obs (_, pc) =  pc

-- -- from instruction (and register value) to leakage instruction
-- leakInst :: Instruction -> Word32 -> LeakInst
-- leakInst (J addr) _ =  LJ addr
-- leakInst (Beq offset) reg = LBeq (reg==0) offset
-- leakInst _ _ = LOther

-- wbToReg :: Word32 -> Maybe Writeback -> Word32
-- wbToReg _ (Just (Write n)) = n
-- wbToReg n Nothing = n


{-# ANN tickRun Spec
  { observation' = 'obs
  , leakage' = 'leakRun
  , simulator' = 'simRun
  , projection' = 'proj
  } #-}
  

isJmp :: Instruction -> Word32 -> Bool
isJmp (J _) _ = True
isJmp (Beq _) reg = (reg == 0)
isJmp _ _ = False


-- | Leakage Description State
data LeakState = LState {
    lreg :: Word32,
    lfetchInstruction :: Instruction
} deriving (Eq, Show)


leakRun :: LeakState -> Word16 -> (LeakState, LeakInst)
leakRun s i = swap $ runState (leak i) s

leak :: MonadState LeakState m => Word16 -> m LeakInst
leak rawInst = do
    state <- get
    let inst = decode rawInst
    let curReg = lreg state
    case (lfetchInstruction state) of 
        Add value -> do
            let result = lreg state + fromIntegral value
            put $ state {lreg = result, lfetchInstruction=inst}
            return LOther
        Clr -> do
            put $ state {lreg = 0, lfetchInstruction=inst}
            return LOther
        J addr -> do
            put $ state {lfetchInstruction=inst}
            return (LJ addr)
        Beq offset ->
            if (lreg state) == 0 
            then do 
                put $ state {lfetchInstruction = Add 0}
                return $ LBeq offset
            else do
                put $ state {lfetchInstruction = inst}
                return LOther
        Out -> do
            put $ state {lfetchInstruction=inst}
            return LOther


-- | Simulation State
data SimState = SimState {
    simPc :: Word8,
    simFetchPc :: Word8
} deriving (Eq, Show)

simRun :: SimState -> LeakInst -> (SimState, Word8)
simRun s i = swap $ runState (sim i) s    


sim :: MonadState SimState m => LeakInst -> m (Word8)
sim leakInst = do 
    state <- get
    let curPC = simPc state
    case leakInst of
        LOther -> do
            put $ state {simPc = curPC+1, simFetchPc = curPC}
            return $ curPC+1
        LJ addr -> do
            put $ state {simPc = addr, simFetchPc = curPC}
            return addr
        LBeq offset -> do
            let newPc = curPC + offset
            put $ state {simPc = newPc, simFetchPc = curPC}
            return newPc
    
            

proj :: State -> (LeakState, SimState)
proj state = case wb of 
        Just (Write newReg) ->
            (LState {lreg = newReg, lfetchInstruction =  fetchInstruction state},
            SimState {simPc = pc state, simFetchPc=fetchPC state})
        Nothing ->
            (LState {lreg = reg state, lfetchInstruction =  fetchInstruction state},
            SimState {simPc = pc state, simFetchPc=fetchPC state})
    where 
    (wb, _) = writebackOut state 