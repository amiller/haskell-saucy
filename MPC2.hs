{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds, PartialTypeSignatures
  #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}



module MPC2 where

import Control.Concurrent.MonadIO
import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map, (!))
import qualified Data.Map.Strict as Map
import Control.Monad (forever,foldM)

import Data.Poly
import Data.Field.Galois (Prime, toP)
import Data.Vector (Vector,forM,fromList)

import ProcessIO
import StaticCorruptions
import Polynomial
import Safe
import OptionallyLeak

data Void
instance Show Void where show x = undefined

type Sh = String

data FmpcOp sh = INPUT sh
               | INPUTx sh Fq
               | OPEN sh
               | ADD sh sh sh deriving (Eq, Show, Functor)

data FmpcRes sh = FmpcRes_Ok
                | FmpcRes_Fq Fq deriving (Eq, Show, Functor)


{--
   Now we proceed with filling out the missing definitions of fABB and fMPC.
   The definition is based around two parts,
    I.(A) a handler for every opcode,
    I.(B) a generic shell, that keeps track of the log of all the operations
      and their results, which it can serve to any party upon request.

   The generic shell (B) has a flag to pick either the idealized ABB (for now)
    or more concrete MPC handlers (for later). So here its type is general,
    storing a PolyFq when really just an Fq would do (since for Abb it's
    always just degree-0).

   Remember that the functionality will define a concrete Sh handle type,
    but this will only be important in part (B). For the opcodes (A) these
    treat the handles opaquely too, but this is just for convenience.
 --}

-- I.(A) Opcode handlers
data FmpcP2F sh = FmpcP2F_Op (FmpcOp sh)
                | FmpcP2F_Log
                | FmpcP2F_Input Fq
                | FmpcP2F_MyShare sh
                deriving (Show, Functor)

data FmpcF2P sh = FmpcF2P_Op (FmpcRes sh)
                | FmpcF2P_Log [(FmpcOp sh)] [(FmpcRes sh)]
                | FmpcF2P_Ok    deriving (Show, Functor)

data FmpcLeak sh = FmpcLeak_Op (FmpcOp sh) | FmpcLeak_Log PID deriving Show

type MonadMPC_F m = (MonadFunctionality m,
                     ?n :: Int,
                     ?t :: Int)

fMPC :: (MonadOptionally m, MonadLeak m (FmpcLeak Sh), MonadMPC_F m) => Functionality (FmpcP2F Sh) (FmpcF2P Sh) Void Void Void Void m
fMPC (p2f, f2p) (_,_) (_,_) = do

  -- Log of operations and results
  ops    <- newIORef ([] :: [(FmpcOp Sh)])
  rsps   <- newIORef ([] :: [(FmpcRes Sh)])

  -- Convenience functions for the log
  let appendOp m = modifyIORef ops $ (++ [m])
  let appendResp m = modifyIORef rsps $ (++ [m])
  
  -- Maps share IDs to secrets
  shareTbl <- newIORef (Map.empty :: Map Sh Fq)

  -- Subroutine for handling events in order
  tasks <- newIORef [] -- empty sequence of tasks
  let processNextTask = do
        -- Pop the next tasks from the queue
        q <- readIORef tasks
        let (next : rest) = q
        writeIORef tasks rest
        -- Execute the task
        next

  let optionallyInOrder task = do
      -- Put the task at the *end* of the queue
      modifyIORef tasks $ (++ [task])
      -- Schedule a task to process the *front* of the queue
      optionally processNextTask


  fork $ forever $ do
   (pid,m) <- readChan p2f
   case m of
    -- Anyone can see the log
    FmpcP2F_Log -> do
       leak $ FmpcLeak_Log pid
       log <- readIORef ops
       rsp <- readIORef rsps
       writeChan f2p (pid, FmpcF2P_Log log rsp)

    -- Handling operations
    -- Each operation chosen by IP is processed in three phases:
    --   - (I) it is leaked to the adversary
    --   - (II), it is added to the log, visible to honest parties
    --           this step happens optionally, but in the same sequence
    --   - (III), the result of the operation is added to the log
    --           this step happens optionally, but in the same sequence

    -- Inputs from the Input Party are handled differently, because
    --   (INPUTx x s) comes with the secret s, but we only want the log to show
    --   (INPUT x)    with the handle x.
    FmpcP2F_Op (INPUTx x s) | pid == "InputParty" -> do
        leak $ FmpcLeak_Op (INPUT x) -- (I)
        modifyIORef shareTbl $ Map.insert x s
        optionallyInOrder $ do
          appendOp $ (INPUT x)       -- (II)
          optionallyInOrder $ do
            appendResp FmpcRes_Ok    -- (III)
        writeChan f2p (pid, FmpcF2P_Ok)

    FmpcP2F_Op (INPUT _) | pid == "InputParty" ->
        error "Input party should only use INPUTx"

    -- The rest of the operations are handled with the same three steps,
    -- with a case statement to customize
    FmpcP2F_Op op | pid == "InputParty" -> do
       leak $ FmpcLeak_Op op         -- (I)   Leak the next operation
       optionallyInOrder $ do
         appendOp $ op               -- (II)  Commit the next operation to the log
         optionallyInOrder $ do
           resp <- case op of        -- (III) Carry out the operation and log the result

             OPEN x -> do
               liftIO $ putStrLn "Opening !!"
               s <- readIORef shareTbl >>=  return . (!x)
               return $ FmpcRes_Fq s

             ADD x y z -> do
               sx <- readIORef shareTbl >>=  return . (!x)
               sy <- readIORef shareTbl >>=  return . (!y)
               let sz = sx + sy
               modifyIORef shareTbl $ Map.insert z sz
               return $ FmpcRes_Ok
           
           appendResp $ resp        

  return ()



-----------------
-- Hybrid world 
-----------------
{---
 This models:

 - A bulletin board.
     POST optionally adds a message to the log, leaking right away
     READ returns the log

 - Point to point messaging.
     Any party can send a message to InputParty.

 - Random preprocessing.
     Any Pi can request their share of the next random polynomial.

 - Optionally scheduling.
     Any protocol can register for a callback.

 --}

data BullRandP2F a = BullRandP2F_Post a | BullRandP2F_Read | BullRandP2F_Rand | BullRandP2F_p2inp Sh Fq | BullRandP2F_Optionally Int
   deriving Show
data BullRandF2P a = BullRandF2P_PostOk | BullRandF2P_Log [(PID, a)] | BullRandF2P_Rand Fq | BullRandF2P_p2inp PID Sh Fq | BullRandF2P_Cb Int | BullRandF2P_CbOk
  deriving Show
data BullRandLeak a = BullRandLeak_Post PID a | BullRandLeak_p2inp PID Sh | BullRandLeak_Opt PID
 deriving Show

fBullRand (p2f,f2p) (a2f,f2a) (z2f,f2z) = do
  tblPreprocRand <- newIORef []
  fBullRand_ tblPreprocRand (p2f,f2p) (a2f,f2a) (z2f,f2z)

fBullRand_ :: (Show a,MonadLeak m (BullRandLeak a), MonadOptionally m) => IORef [PolyFq] -> Functionality (BullRandP2F a) (BullRandF2P a) Void Void Void Void m
fBullRand_ tblPreprocRand (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Writes: best effort availability (uses optionally)
  -- Reads:  available to every party immediately
  --         consistent views are guaranteed

  -- Number of parties, tolerance parameter encoded in SID
  let (n :: Int, t :: Int, ssid :: String) = readNote "fBullRand" $ snd ?sid

  -- Counters viewed by each of the participant parties
  let initCtrs = [("P:"++show i, 0) | i <- [1..n]]
  
  log <- newIORef []  -- empty log

  randTbl <- newIORef ([] :: [PolyFq])   -- List of polynomials
  randCtrs <- newIORef $ Map.fromList initCtrs -- Maps PID to index of next poly to access

  fork $ forever $ do
    (pid, mx) <- readChan p2f
    case mx of
      {--- Bulletin board section ---}
      
      BullRandP2F_Post m -> do
        -- Optionally add this to the log
        liftIO $ putStrLn $ "fBullRand:" ++ show mx
        leak $ BullRandLeak_Post pid m
        optionally $ do
            -- liftIO $ putStrLn $ "Posting in the bulletin board"
            modifyIORef log (++ [(pid,m)])
            ?pass
            
        writeChan f2p $ (pid, BullRandF2P_PostOk)

      BullRandP2F_Read -> do
        -- Send this party the whole log
        l <- readIORef log
        writeChan f2p $ (pid, BullRandF2P_Log l)

      BullRandP2F_p2inp sh s -> do
        -- This party is sending to InputParty
        leak $ BullRandLeak_p2inp pid sh
        optionally $ do
            writeChan f2p ("InputParty", BullRandF2P_p2inp pid sh s)
        writeChan f2p (pid, BullRandF2P_PostOk)

      {--- Random preprocessing section ---}
      BullRandP2F_Rand -> do
        -- Send this party their next RAND
        let i = case pid of "P:1" -> 1
                            "P:2" -> 2
                            "P:3" -> 3
                            _ -> error "RAND called by someone else"
        tbl <- readIORef randCtrs
        let ctr = tbl ! pid
        rnd <- readIORef randTbl
        if ctr == length rnd then do
          phi <- randomDegree t
          modifyIORef randTbl (++ [phi])
        else return ()
        rnd <- readIORef randTbl
        modifyIORef randCtrs $ Map.insert pid (ctr + 1)
        let s = eval (rnd !! ctr) i
        writeChan f2p $ (pid, BullRandF2P_Rand s)


      {--- Callback requests ---}
      -- Enable parties to request a callback
      -- We'll use this in order to wait for events posted to the
      -- bulletin board
      BullRandP2F_Optionally cb -> do
        leak $ BullRandLeak_Opt pid
        optionally $ writeChan f2p (pid, BullRandF2P_Cb cb)
        writeChan f2p (pid, BullRandF2P_CbOk)

  return ()


{---
 Implementation
---}


data SharingPost = SharingPost_Op (FmpcOp Sh)
                 | SharingPost_Input Sh Fq
                 | SharingPost_Share Sh Fq deriving Show


protSharingIP :: (MonadOptionallyP m) => Protocol (FmpcP2F Sh) (FmpcF2P Sh) (BullRandF2P SharingPost) (BullRandP2F SharingPost) m
protSharingIP (z2p, p2z) (f2p, p2f) = do

  -- Number of parties, tolerance parameter encoded in SID
  let (n :: Int, t :: Int, ssid :: String) = readNote "protSharingIP" $ snd ?sid

  -- Keep track of all the openings seen
  shareTbl <- newIORef Map.empty   -- Maps Sh -> Map -> Sh

  myShares <- newIORef Map.empty   -- isServer=True only
  myInpMask <- newIORef Map.empty   -- isServer=True only

  -- Keep track of the input masks received (InputParty only)
  inputMasks <- newIORef (Map.empty :: Map Sh Fq)
  inputMaskShares <- newIORef Map.empty

  let (isServer,i) = case ?pid of
                       "P:1" -> (True,1)
                       "P:2" -> (True,2)
                       "P:3" -> (True,3)
                       _ -> (False,-1)

  -- We'll split the f2p channel into several parts we can wait individually
  chanRand <- newChan
  chanLog <- newChan  
  chanPostOk <- newChan

  fork $ forever $ do
    mf <- readChan f2p
    case mf of
          BullRandF2P_Rand s -> writeChan chanRand s
          BullRandF2P_PostOk -> writeChan chanPostOk ()
          BullRandF2P_p2inp pid x s | ?pid == "InputParty" -> do
              -- Add this input to input Masks
              let j = case pid of "P:1" -> 1
                                  "P:2" -> 2
                                  "P:3" -> 3
              alreadyStarted <- readIORef inputMaskShares >>= return . member x
              if not alreadyStarted then modifyIORef inputMaskShares $ Map.insert x Map.empty
              else return ()
              shrs <- readIORef inputMaskShares >>= return . (! x)
              let shrs' = Map.insert j s shrs
              if Map.size shrs' == n then do
                 -- liftIO $ putStrLn $ "Have enough to interpolate input mask"
                 -- TODO: Robust interpolation
                 let phi :: PolyFq = polyInterp (Map.toList shrs')
                 modifyIORef inputMasks $ Map.insert x (eval phi 0)
                 -- liftIO $ putStrLn $ "Shares:" ++ show shrs'
                 -- liftIO $ putStrLn $ "Poly:" ++ show phi
              else return ()
              modifyIORef inputMaskShares $ Map.insert x shrs'
              -- liftIO $ putStrLn $ "Finished receiving input mask share, passing"
              ?pass

          BullRandF2P_Log log -> do
            writeChan chanLog log

          _ -> error "?"
    return ()


  -- Maintain a virtual log of completed operations (to emulate Fmpc)
  virtOps <- newIORef []
  virtRsps <- newIORef []

  -- Process one bulletin board item at a time
  let handleLog item = do
        -- liftIO $ putStrLn $ "Handling log: " ++ show item
        case item of
          (pid, SharingPost_Op (INPUT x)) | pid == "InputParty" && isServer -> do
            -- Fetch our share of a fresh random [r]
            writeChan p2f $ BullRandP2F_Rand
            sr <- readChan chanRand

            -- Send this share to the input party
            writeChan p2f $ BullRandP2F_p2inp x sr
            () <- readChan chanPostOk

            -- Store the sr for the next call
            modifyIORef myInpMask $ Map.insert x sr
            return ()

          (pid, SharingPost_Op (OPEN x)) | pid == "InputParty" && isServer -> do
            -- Fetch our share of this value and post it
            sx <- readIORef myShares >>= return . (! x)
            writeChan p2f $ BullRandP2F_Post $ SharingPost_Share x sx
            () <- readChan chanPostOk
            return ()

          (pid, SharingPost_Input x mr) | pid == "InputParty" && isServer -> do
            -- Read the sr previously stored
            sr <- readIORef myInpMask >>= return . (! x)

            -- Store this share
            modifyIORef myShares $ Map.insert x (mr - sr)

            -- Mark the operation as committed and completed
            modifyIORef virtOps  $ (++ [INPUT x])
            modifyIORef virtRsps $ (++ [FmpcRes_Ok])
            return ()

          (pid, SharingPost_Share x s) -> do
            -- Update the share table
            tbl <- readIORef shareTbl
            if not (member x tbl) then do
              -- Initialize the map
              modifyIORef shareTbl $ Map.insert x Map.empty
            else return()

            let j = case pid of "P:1" -> 1
                                "P:2" -> 2
                                "P:3" -> 3
            -- Are there N now? If so, the share is available and we can decode
            shrs <- readIORef shareTbl >>= return . (! x)
            let shrs' = Map.insert j s shrs
            if Map.size shrs' == n then do
                 -- liftIO $ putStrLn $ "Have enough to interpolate input mask"
                 -- TODO: Robust interpolation
                 let phi :: PolyFq = polyInterp (Map.toList shrs')

                 -- Add this to the outputs
                 modifyIORef virtRsps (++ [FmpcRes_Fq (eval phi 0)])

            else return ()
            modifyIORef shareTbl $ Map.insert x shrs'

            return ()

          _ -> do
            -- liftIO $ putStrLn $ "Uninterested log item: " ++ show item
            return ()

  -- Only process the new bulletin board entries since last time
  logCtr <- newIORef 0

  let syncLog = do
      -- Ask the functionality to send the log
      writeChan p2f BullRandP2F_Read
      -- Read the log from local channel
      log <- readChan chanLog
      -- Only process the new elements
      t <- readIORef logCtr
      let tail = drop t log
      modifyIORef logCtr (+ length tail)
      forM (fromList tail) $ handleLog
      return  ()

  -- Here's how we implement waiting for an event on the bulletin board
  -- We'll schedule an "optionally" task that checks the bulletin board
  -- If the condition isn't satisfied yet, schedule another (and then pass)
  let waitUntil checkCond = do
      proceed <- newChan
      let _loop = do
          ?optionally $ do
             -- Run the condition checker
             b <- checkCond
             -- Exit the loop and carry out the rest
             if b then writeChan proceed ()
             -- Otherwise schedule another task
             else do
               _loop
               ?pass
      _loop
      return proceed

  -- Handle environment inputs
  fork $ forever $ do
    mf <- readChan z2p
    case mf of
      FmpcP2F_Op (INPUTx x s) | ?pid == "InputParty" -> do
        -- Post this to the board
        writeChan p2f $ BullRandP2F_Post $ SharingPost_Op (INPUT x)
        () <- readChan chanPostOk
        sat <- waitUntil $ do
           -- Wait until we've received all the input mask shares
           b <- readIORef inputMasks >>= return . member x
           return b
        fork $ do
           () <- readChan sat
           -- liftIO $ putStrLn $ "We've received enough Shares! Posting to the bulletin"
           r <- readIORef inputMasks >>= return . (! x) 
           let mr = s + r
           writeChan p2f $ BullRandP2F_Post $ SharingPost_Input x mr
           () <- readChan chanPostOk
           ?pass

        writeChan p2z $ FmpcF2P_Ok

      FmpcP2F_Op (INPUT _) | ?pid == "InputParty" -> error "should only call inputx"

      FmpcP2F_Op op | ?pid == "InputParty" -> do
        syncLog
        writeChan p2f $ BullRandP2F_Post $ SharingPost_Op (op)
        () <- readChan chanPostOk
        writeChan p2z $ FmpcF2P_Ok
        

      FmpcP2F_Log -> do
        syncLog
        -- Return the synchronized log...
        ops <- readIORef virtOps
        rsps <- readIORef virtRsps
        writeChan p2z $ FmpcF2P_Log ops rsps
        

  -- Whenever we're initialized, go ahead and begin requesting to see the board
  let isServer = True
  if isServer then
     return ()
  else
     return ()
  return ()



--- This test environment should give a good coverage of all the interesting real-world protocol behaviors.
envTestMPC :: MonadEnvironment m =>
  Environment              (FmpcF2P Sh)                    (FmpcP2F Sh)
              (SttCruptA2Z (OptionalF2P (BullRandF2P SharingPost)) (OptionalF2A (LeakF2A (BullRandLeak SharingPost) Void)))
              (SttCruptZ2A (OptionalP2F (BullRandP2F SharingPost)) (OptionalA2F (LeakA2F Void)))
              Void Void String m
envTestMPC z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
   -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("mpc",show (3,1,"")) (Map.fromList [("Observer",()),("P:1",())])

  -- Opened Values
  openTable <- newIORef $ Map.fromList [("P:"++show i, []) | i <- [1.. 3]]
  lastHandle <- newIORef Nothing
  lastIntHandle <- newIORef Nothing

  let sendInput ipp2f = do
        writeChan z2p $ ("InputParty", ipp2f)
   
  fork $ forever $ do
    (pid,m) <- readChan p2z
    printEnvIdeal $ "[" ++ pid ++ "] sent " ++ show m
    ?pass

  fork $ forever $ do
    mf <- readChan a2z
    case mf of
      SttCruptA2Z_F2A (OptionalF2A_Pass) -> ?pass
      SttCruptA2Z_P2A (pid, m) -> do
        -- Store the concrete handles received from corrupt party
        case m of
          OptionalF2P_Through (BullRandF2P_Log log) | pid == "Observer" -> do
            printEnvReal $ "[" ++pid++ "] (corrupt) received log: "
            liftIO $ putStr $ "\ESC[34m"
            forM (fromList log) $ liftIO . putStrLn . show
            liftIO $ putStr $ "\ESC[0m"
          _ -> do
            printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
        ?pass
      _ -> error $ "Help!" ++ show mf
      
  -- Send inputs through honest InputParty
  () <- readChan pump; liftIO $ putStrLn "pump"
  sendInput $ (FmpcP2F_Op $ INPUTx "X" 2)

  -- Deliver the next event (complete the post to bulletin)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- Let all honest parties sync to the log
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p $ ("P:2", FmpcP2F_Log)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p $ ("P:3", FmpcP2F_Log)

  -- Deliver the next events (all three parties send to IP)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- Send a bogus share to the honest party, then deliver
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2P $ ("P:1", OptionalP2F_Through $ BullRandP2F_p2inp "X" 0)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- At this point the InputParty can resume, posting to the bulletin
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_DeliverProt "InputParty"
  
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- Logs from Observer (a corrupt party)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2P ("Observer", (OptionalP2F_Through BullRandP2F_Read))

  
  -- Let all honest parties sync to the log
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p $ ("P:2", FmpcP2F_Log)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p $ ("P:3", FmpcP2F_Log)


  -- Begin the OPEN phase (interleaved with INPUT, but this is fine)
  () <- readChan pump; liftIO $ putStrLn "pump"
  liftIO $ putStrLn $ "about to post open"
  sendInput $ (FmpcP2F_Op $ OPEN "X")
  
  -- Deliver the next event (complete the post to bulletin)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- Let all honest parties sync to the log
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p $ ("P:2", FmpcP2F_Log)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p $ ("P:3", FmpcP2F_Log)

  -- Deliver the next events (all honest parties post their shares)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- Have the adversary post a share and deliver it
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2P $ ("P:1", OptionalP2F_Through $ BullRandP2F_Post $ SharingPost_Share "X" 0)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- Logs from Observer (a corrupt party)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2P ("Observer", (OptionalP2F_Through BullRandP2F_Read))  

  -- Logs from an honest party
  () <- readChan pump; liftIO $ putStrLn "pump"  
  sendInput $ FmpcP2F_Log

  -- Let all honest parties sync to the log
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p $ ("P:2", FmpcP2F_Log)
  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p $ ("P:3", FmpcP2F_Log)
  

  () <- readChan pump
  writeChan outp "environment output: 1"



runMPCFunc :: MonadFunctionality m => Int -> Int ->
    (MonadMPC_F m => Functionality a b c d e f m) ->
     Functionality a b c d e f m
runMPCFunc n t f = let ?n = n; ?t = t in f


testMpc1Real = runITMinIO 120 $ execUC envTestMPC (runOptLeakP protSharingIP) (runOptLeak $ fBullRand) dummyAdversary



{---
 
 ---}
simSharing :: MonadAdversary m => Adversary (SttCruptZ2A (OptionalP2F (BullRandP2F SharingPost)) (OptionalA2F (LeakA2F Void))) (SttCruptA2Z (OptionalF2P (BullRandF2P SharingPost)) (OptionalF2A (LeakF2A (BullRandLeak SharingPost) Void))) (OptionalF2P (FmpcF2P Sh)) (OptionalP2F (FmpcP2F Sh)) (OptionalF2A (LeakF2A (FmpcLeak Sh) Void)) (OptionalA2F (LeakA2F Void)) m
simSharing (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  
  -- Number of parties, tolerance parameter encoded in SID
  let (n :: Int, t :: Int, ssid :: String) = readNote "protSharingIP" $ snd ?sid
  
  let isCruptIP = member "InputParty" ?crupt 

  {--
   The main strategy is that the simulator will maintain a local sandbox execution of
         a real UC experiment that's kept in the same configuration as the ideal world.
   The environment/dummyAdversary interface is routed directly to this virtualized execution.

   Whenever an honest party in this simulation outputs a value, we'll need to activate the
     ideal functionality to cause the same event to happen through the dummy protocol.

   In the honest IP case:
      We will need to extract the input value. When a simulated honest party outputs INPUT "X",
            we need to pass INPUT "X" s to the ideal functionality.
         
      We can do this by reading from the simulated preprocessing table.

   In the Corrupt IP case:
      We need to equivocate. We'll have to show Z preprocessing values for corrupt parties
           prior to learning the secret s. Later when s is revealed, we'll have to disclose
           the entire preprocessing polynomial and it needs to be consistent.

      We can do this by modifying the preprocessing table to incorporate new information
           as we receive it from the ideal functionality.
           The `t` random values we initially disclose will come from fBullRand's sampled
           polynomial, but we'll update it when we learn `s`.
  --}

  sbxTblPreprocRand <- newIORef []
  let sbxBullRand () = fBullRand_ sbxTblPreprocRand

  -- Routing z2a <-->  
  sbxpump <- newChan
  sbxz2p <- newChan   -- writeable by host
  sbxp2z <- newChan   -- readable by host
  let sbxEnv z2exec (p2z',z2p') (a2z',z2a') _ pump' outp' = do
        -- Copy the SID and corruptions
        writeChan z2exec $ SttCrupt_SidCrupt ?sid ?crupt

        -- Expose wrappers for the p2z interactions.
        forward p2z' sbxp2z
        forward sbxz2p z2p'

        -- Forward messages from environment to host, into the sandbox dummy adv
        forward z2a z2a'
        forward a2z' a2z

        -- When the sandbox receives on pump', pass control back to the host
        forward pump' sbxpump

        return ()

  chanLog <- newChan
  fork $ forever $ do
    (pid, mf) <- readChan p2a
    case mf of
      OptionalF2P_Deliver -> undefined
      OptionalF2P_Through FmpcF2P_Ok -> undefined
      OptionalF2P_Through (FmpcF2P_Log ops rsps) -> do
          writeChan chanLog $ FmpcF2P_Log ops rsps
      _ -> do
        liftIO $ putStrLn "receive from ideal"
        error "receive from ideal"

  let handleLeak m = do
      case m of
       (_, FmpcLeak_Op (INPUT x)) -> do
         if isCruptIP then
           return ()
         else do
           -- We've learned the next operation will be an input, but we can't extract yet.
           -- Need to initiate the sandbox simulation with an arbitrary input
           writeChan sbxz2p ("InputParty",  (FmpcP2F_Op (INPUTx x 0)))
           mf <- readChan sbxp2z
           let ("InputParty", FmpcF2P_Ok) = mf
           return ()

       (_, FmpcLeak_Log pid) -> do
           if not (member pid ?crupt) then do
              -- liftIO $ putStrLn $ "honest FmpcLeak_Log"
              writeChan sbxz2p (pid,  FmpcP2F_Log)
              mf <- readChan sbxp2z
              let (_, FmpcF2P_Ok) = mf
              return ()
           else
              return ()
           return ()

       _ -> error "hmm"

  -- Only process the new bulletin board entries since last time
  leakCtr <- newIORef 0
  let syncLeaks () = do
        writeChan a2f $ OptionalA2F_Through $ LeakA2F_Get
        mf <- readChan f2a
        let OptionalF2A_Through (LeakF2A_Leaks leaks) = mf
        printAdv $ "Leaks: " ++ show leaks
        -- Only process the new elements
        t <- readIORef leakCtr
        let tail = drop t leaks
        modifyIORef leakCtr (+ length tail)
        forM (fromList tail) $ handleLeak
        return  ()

  -- Only process the new items since last time
  let handleItem item = do
      printAdv $ "Handle Item: " ++ show item
      undefined
      return ()

  opsCtr <- newIORef 0
  rspsCtr <- newIORef 0
  let syncLog () = do
      -- TODO: pick one of the corrupt parties
      printAdv $ "SyncLog: "
      writeChan a2p $ ("P:1", OptionalP2F_Through $ FmpcP2F_Log)
      -- Read the log from log channel
      log <- readChan chanLog
      let (FmpcF2P_Log ops rsps) = log
      -- Only process the new elements
      t <- readIORef opsCtr
      let tail = drop t ops
      modifyIORef opsCtr (+ length tail)
      forM (fromList tail) $ handleItem
      return  ()

  let sbxAdv (z2a',a2z') (p2a',a2p') (f2a',a2f') = do
        -- The sandbox adversary poses as the dummy adversary, but takes every
        -- activation opportunity to synchronize with the ideal world functionality
        fork $ forever $ do
          mf <- readChan z2a'
          printAdv $ show "Intercepted z2a'" ++ show mf
          syncLeaks ()
          syncLog ()
          printAdv $ "SyncLeaks Done"
          case mf of
            SttCruptZ2A_A2F f -> writeChan a2f' f
            SttCruptZ2A_A2P pm -> writeChan a2p' pm
        fork $ forever $ do
          m <- readChan f2a'
          liftIO $ putStrLn $ show "f2a'"
          writeChan a2z' $ SttCruptA2Z_F2A m
        fork $ forever $ do
          (pid,m) <- readChan p2a'
          liftIO $ putStrLn $ show "p2a'"
          writeChan a2z' $ SttCruptA2Z_P2A (pid, m)
        return ()


  -- We need to wait for the write token before we can finish initalizing the
  -- sandbox simulation.
  mf <- selectRead z2a f2a   -- TODO: could there be a P2A here?

  fork $ execUC sbxEnv (runOptLeakP protSharingIP) (runOptLeak (sbxBullRand ())) sbxAdv
  () <- readChan sbxpump

  -- After initializing, the sbxAdv is now listening on z2a,f2a,p2a. So this passes to those
  case mf of
    Left m -> writeChan z2a m
    Right m -> writeChan f2a m
      
  fork $ forever $ do
      () <- readChan sbxpump
      undefined
      return ()
  return ()

testMpc1Ideal = runITMinIO 120 $ execUC envTestMPC (runOptLeakP idealProtocol) (runOptLeak $ runMPCFunc 3 1 fMPC) simSharing
