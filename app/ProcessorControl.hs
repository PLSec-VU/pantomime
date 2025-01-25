{-# LANGUAGE FlexibleContexts #-}

module ProcessorControl
    ( test
    ) where
--import Test.QuickCheck

import Data.Word
import Data.Bits
import Control.Monad.State (MonadState, MonadIO, put, get, runStateT, runState, liftIO)
import Data.Maybe (isJust)
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

encode :: Instruction -> Word16
encode instruction = case instruction of
    Add value -> (0 `shiftL` 8) .|. fromIntegral value
    Clr       -> 1 `shiftL` 8
    Out       -> 2 `shiftL` 8
    J addr    -> (3 `shiftL` 8) .|. fromIntegral addr
    Beq off   -> (4 `shiftL` 8) .|. fromIntegral off

decode :: Word16 -> Instruction
decode word = case shiftR word 8 of
    0 -> Add (fromIntegral (word .&. 0xFF))
    1 -> Clr
    2 -> Out
    3 -> J (fromIntegral (word .&. 0xFF))
    4 -> Beq (fromIntegral (word .&. 0xFF))
    _ -> error "Invalid instruction"

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
    -- instruction should be ignored
    bubble :: Bool,
    -- needed for jumps
    nextPc :: Word8,
    -- pipeline registers
    fetchPC :: Word8,
    fetchInstruction :: Instruction,
    writebackOut :: (Maybe Writeback, Maybe Output)
} deriving (Eq, Show)

-- Helper types remain the same
newtype Output = Val Word32 deriving (Eq, Show)
newtype Writeback = Write Word32 deriving (Eq, Show)

-- -- | Pipeline Stages
fetch :: MonadState State m => Word16 -> m Word8
fetch rawInstr = do
    state <- get
    let inst = if bubble state 
               then Add 0  -- No-op
               else decode rawInstr
    put $ state {
        fetchInstruction = inst,
        fetchPC = pc state,
        pc = nextPc state ,
        bubble = False  
        -- ^ Clear bubble flag after using it
    }
    return $ nextPc state 

execute :: MonadState State m => m ()
execute = do 
    state <- get
    let inst = fetchInstruction state
    case inst of
        Add value -> 
            let result = reg state + fromIntegral value in
            put $ state {writebackOut = (Just $ Write result, Nothing), nextPc = pc state + 1}
        Clr ->
            put $ state {writebackOut = (Just (Write 0), Nothing), nextPc = pc state + 1}
        Out ->
            put $ state {writebackOut = (Nothing, Just $ Val (reg state)), nextPc = pc state + 1}
        J addr ->
            put $ state {
                writebackOut = (Nothing, Nothing),
                bubble = True,
                nextPc = addr  
                -- ^ Mark next instruction as invalid
            }
        Beq offset ->
            if reg state == 0 
            then put $ state {
                writebackOut = (Nothing, Nothing),
                bubble = True,  
                -- ^ Mark next instruction as invalid
                nextPc = fetchPC state + offset
            }
            else put $ state {writebackOut = (Nothing, Nothing), nextPc = pc state + 1}


writeback :: MonadState State m => m (Maybe Output)
writeback = do
   state <- get
   let (wb, out) = writebackOut state
   -- Update register if there's a writeback
   put state{
       reg = maybe (reg state) (\(Write v) -> v) wb
   }
   return out


tick :: MonadState State m => Word16 -> m (Maybe Output, Word8)
tick rawInst = do
   --(out, pc) <- writeback
   out <- writeback
   execute 
   pc <- fetch rawInst
   return (out, pc)

test :: IO ()
test = do
   putStrLn "Test 1: Jump"
   runAndShow prog1
   putStrLn "\nTest 2: Sequential with Add"
   runAndShow prog2
 where
   prog1 = [Out, J 3, Add 5, Add 10, Out, Out, Out, Out]  -- Should output 0, 10, 10
   prog2 = [Add 1, Out, Clr, Out, Beq 2, Out, Add 2, Out, Out, Out, Out]  -- Should output 1, 1, 3

   runAndShow prog = do
       (outs, s) <- runStateT (run $ map encode prog) initState
       putStrLn $ "State: " ++ show s
       putStrLn $ "Outputs: " ++ show outs

   initState = State { 
       pc = 0, 
       nextPc = 1,
       reg = 0, 
       bubble = False,
       fetchInstruction = Add 0,
       writebackOut = (Nothing, Nothing)
   }

run :: MonadState State m => [Word16] -> m [(Maybe Output,Word8)]
run program = do
   state <- get
   if pc state >= fromIntegral (length program) 
   then return []
   else do
       let inst = program !! fromIntegral (pc state)
       out <- tick inst
       os <- run program
       return $ out:os

