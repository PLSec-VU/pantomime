{-# LANGUAGE FlexibleContexts #-}

module ProcessorModular
    ( test
    , fetchRun
    , obsFetch
    , leakFetch
    , simFetchRun
    , fetchProj
    ) where
--import Test.QuickCheck

import Data.Word
import Data.Bits
import Control.Monad.State (MonadState, MonadIO, put, get, runStateT, runState, liftIO) 
import Data.Maybe (fromMaybe,isJust)
import Data.Tuple (swap)
import Projection
import UC
--import Test.QuickCheck hiding ((.&.))

data Instruction = Add Word8
                -- ^ Add immediate to the register
                |  Clr
                -- ^ Reset the register to zero
                |  Out 
                -- ^ Output the register value
                deriving (Eq, Ord, Show) 

-- |Instruction encoding schema:
--
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
encode :: Instruction -> Word16
encode instruction = case instruction of
    Add value -> (0 `shiftL` 8) .|. fromIntegral value
    Clr       -> 1 `shiftL` 8
    Out       -> 2 `shiftL` 8

decode :: Word16 -> Instruction
decode word = case shiftR word 8 of
    0 -> Add (fromIntegral (word .&. 0xFF))
    1 -> Clr
    2 -> Out
    _ -> error "Invalid instruction"

-- | Processor State
data State = State {
    -- fetch
    pc :: Word8,
    -- wb
    reg :: Word32,
    -- ex
    stalled :: Bool,
    -- fetch
    fetchInstruction :: Instruction,
    -- ex
    writebackOut :: (Maybe Writeback, Maybe Output)
} deriving (Eq, Show)


newtype Output = Val Word32 deriving (Eq, Show)
newtype Writeback = Write Word32 deriving (Eq, Show)

-- | Pipeline Stages

fetch :: MonadState State m => Bool -> Word16 -> Maybe Output -> m (Instruction, Maybe Output)
fetch stalled rawInstr out = do
    state <- get 
    -- updating execute's new instruction
    if stalled then return (fetchInstruction state, out)
    else do 
        let newPc = pc state + 1
        put $ state {pc = newPc}
        return (decode rawInstr, out)

execute :: MonadState State m => Word32 ->  Instruction -> Maybe Output -> Word16  -> m (Bool, Word16, Maybe Writeback, Maybe Output,  Maybe Output)
execute reg instr out curInst = do 
    state <- get
    --let instr = fetchInstruction state
    case instr of
        Add value ->
            -- | stalled or fast-path, execute now.
            if stalled state || value == 0 then do -- || reg state == 0 then do
                let result = Just $ Write $ reg + fromIntegral value
                return (False, curInst, result, Nothing, out)
            -- | slow-path, stall the pipeline for one tick.                        
            else do
                return (True, curInst, Nothing, Nothing, out)
        Clr ->
                return (False, curInst, Just (Write 0),  Nothing, out)
        Out ->
                return (False, curInst, Nothing, Just $ Val reg, out)

writeback :: MonadState State m => Word16 -> m (Word16, Maybe Output, Word32)
writeback instr = do
        state <- get
        let (wb, out) = writebackOut state
        return (instr, out, maybe (reg state) (\(Write v) -> v) wb)


tick :: (MonadState State m, MonadIO m) => Word16 -> m (Maybe Output, Word8)
tick rawInst = do
    state <- get
    -- writeback
    (rawInst, out, newReg) <- writeback rawInst
    put $ state {reg = newReg}
    -- execute
    state <- get
    (stall, rawInst, wb, wbout, out) <- execute (reg state) (fetchInstruction state) out rawInst  
    put $ state {stalled = stall, writebackOut = (wb, wbout)} 
    -- fetch
    (inst, out) <- fetch stall rawInst out 
    state <- get
    put $ state {fetchInstruction = inst}
    -- outputs
    return (out, pc state)
    
run :: (MonadState State m,  MonadIO m) => [Word16] -> m ()
run program = do
    state <- get
    if pc state >= fromIntegral (length program) 
    then return ()
    else 
        do
        let inst = program !! fromIntegral (pc state)
        (out, _) <- tick inst
        liftIO $ putStrLn $ "Output:" ++ show out
        run program

test :: IO ()
test = do 
    (_, s) <- runStateT (run bin) initState
    putStrLn $ "halted, with final state" ++ show s
    where 
      --prog = [Out, Add 2, Out, Add 3, Out, Clr, Out]  
      --prog = [Out, Add 2, Out, Clr, Out, Add 3, Out]  
      prog = [Out, Add 1, Out, Add 0, Out, Clr, Out, Add 41, Out, Add 1, Out, Out, Out, Out,Out, Out, Out, Out]  
      --prog = [Add 1, Out, Out, Out, Out]  
      bin  = map encode prog
      initState = State { pc = 0, reg = 0, stalled = False, fetchInstruction = Add 0, writebackOut = (Nothing, Nothing)}
      
------------------------------------------------------------------------------------
-- Leakage Description and Proof
------------------------------------------------------------------------------------

-- | Simulator instructions
data LeakInst = LAdd Bool
                |  LOut 
                |  LClr
    deriving (Eq, Ord, Show) 

-- Instruction leakage
leakInst :: Instruction -> LeakInst
leakInst inst = case inst of
    Add imm -> LAdd $ imm==0
    Out     -> LOut
    Clr     -> LClr

-- | We leak the current instruction and whether it triggers the fast-path.
leak :: () -> Word16 -> ((), LeakInst)
leak _ rawInst = ((), leakInst inst)
    where
    inst = decode rawInst

-- | Attacker can see whether there's an ouput + the PC.
obs :: (Maybe Output, Word8) -> (Bool, Word8)
obs (Just _, pc) = (True, pc)
obs (_, pc) = (False, pc)

-- | Simulation State
data LState = LState {
    --lpc :: Word8,
    lstalled :: Bool,
    lFetchInst :: LeakInst,
    lWBout :: Bool
} deriving (Eq, Show)

-- | Fetch Proof

{-# ANN fetchRun UC
  { observation = 'obsFetch
  , leakage = 'leakFetch
  , simulator = 'simFetchRun
  , projection = 'fetchProj
} #-}

obsFetch :: () -> (Instruction, Maybe Output) -> ((), (LeakInst, Bool))
obsFetch _ (inst, out) = ((), (leakInst inst, isJust out))

leakFetch :: () -> (Bool, Word16, Maybe Output) -> ((), (Bool, LeakInst, Bool))
leakFetch _ (stalled, rawInstr, out) = ((), (stalled, leakInst $ decode rawInstr, isJust out))

fetchRun :: State -> (Bool,  Word16,  Maybe Output) -> (State, (Instruction, Maybe Output))
fetchRun s (stalled, rawInstr, out) = swap $ runState (fetch stalled rawInstr out) s   

simFetchRun :: LState -> (Bool, LeakInst, Bool) -> (LState, (LeakInst, Bool))
simFetchRun s (stalled, inst, out) = swap $ runState (simFetch stalled inst out) s   

simFetch :: MonadState LState m => Bool -> LeakInst -> Bool -> m (LeakInst, Bool)
simFetch stalled inst out = do
    state <- get
    if stalled then return (lFetchInst state, out)
    else do 
        return (inst, out) 

fetchProj :: State -> ((), LState)
fetchProj s = ((), ls)
    where    
    ls = LState{ 
        lstalled = stalled s
        , lFetchInst = leakInst $ fetchInstruction s
        , lWBout = isJust $ snd $ writebackOut s
    }

-- | Writeback Proof

-- writeback :: MonadState State m => m (Maybe Output, Word32)
-- writeback = do
--         state <- get
--         let (wb, out) = writebackOut state
--         return (out, maybe (reg state) (\(Write v) -> v) wb)


-- wbRun :: State -> (State, (Maybe Output, Word8))
-- wbRun s = swap $ runState writeback s   

-- simWBRun :: LState -> (LState, (Bool, Word8))
-- simWBRun s = swap $ runState simWB s   

-- simWB :: MonadState LState m => m (Bool, Word8)
-- simWB = do
--     state <- get
--     return (lWBout state, lpc state)