 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures
  #-} 

module ACast where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map)
import Data.List (elemIndex, delete)
import qualified Data.Map.Strict as Map

{- fACast: an asynchronous broadcast functionality, Bracha's Broadcast -}
{-
   Narrative description:
 -}


data ACastP2F a = ACastP2F_Input a deriving Show
data ACastF2P a = ACastF2P_OK | ACastF2P_Deliver a deriving (Show, Eq)
--data ACastA2F a = ACastA2F_Deliver PID deriving Show


fACast :: MonadFunctionalityAsync m a => Functionality (ACastP2F a) (ACastF2P a) Void Void Void Void m
fACast (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender, set of parties, and tolerance parameter is encoded in SID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "fACast" $ snd ?sid


  -- Check the fault tolerance parameters
  let n = length parties
  require (Map.size ?crupt <= t) "Fault tolerance assumption violated"
  require (3*t < n) "Invalid fault tolerance parameter (must be 3t<n)"

  -- Allow sender to choose the input
  (pid, ACastP2F_Input m) <- readChan p2f
  liftIO $ putStrLn $ "[fACast]: input read " -- ++ show m
  leak m
  require (pid == pidS) "Messages not from sender are ignored"

  -- Every honest party eventually receives an output
  forMseq_ parties $ \pj -> do
    eventually $ writeChan f2p (pj, ACastF2P_Deliver m)

  writeChan f2p (pidS, ACastF2P_OK)



{- Protocol ACast -}

data ACastMsg t = ACast_VAL t | ACast_ECHO t | ACast_READY t deriving (Show, Eq, Read)

-- Give (fBang fMulticast) a nicer interface
manyMulticast :: MonadProtocol m =>
     PID -> [PID]
     -> (Chan (SID, (MulticastF2P t)), Chan (SID, t))
     -> m (Chan (PID, t), Chan t, Chan ())
manyMulticast pid parties (f2p, p2f) = do
  p2f' <- newChan
  f2p' <- newChan
  cOK <- newChan

  -- Handle writing
  fork $ forMseq_ [0..] $ \(ctr :: Integer) -> do
       m <- readChan p2f'
       let ssid = (show ctr, show (pid, parties, ""))
       writeChan p2f (ssid, m)

  -- Handle reading (messages delivered in any order)
  fork $ forever $ do
    (ssid, mf) <- readChan f2p
    let (pidS :: PID, _ :: [PID], _ :: String) = readNote "manyMulti" $ snd ssid
    case mf of
      MulticastF2P_OK -> do
                     require (pidS == pid) "ok delivered to wrong pid"
                     writeChan cOK ()
      MulticastF2P_Deliver m -> do
                     writeChan f2p' (pidS, m)
  return (f2p', p2f', cOK)

readBangMulticast pid parties f2p = do
  c <- newChan
  fork $ forever $ do
    forMseq_ [0..] 

writeBangSequential p2f = do
  c <- newChan
  fork $ do
    forMseq_ [0..] $ \(ctr :: Integer) -> do
        m <- readChan c
        let ssid' = ("", show ctr)
        writeChan p2f (ssid', m)
  return c

readBangAnyOrder f2p = do
  c <- newChan
  fork $ forever $ do
    (_, m) <- readChan f2p
    writeChan c m
  return c

protACast :: MonadAsyncP m => Protocol (ClockP2F (ACastP2F String)) (ACastF2P String) (SID, MulticastF2P (ACastMsg String)) (SID, ACastMsg String) m
protACast (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid
  cOK <- newChan

  -- Keep track of state
  inputReceived <- newIORef False
  decided <- newIORef False
  echoes <- newIORef (Map.empty :: Map String (Map PID ()))
  readys <- newIORef (Map.empty :: Map String (Map PID ()))
                   
  -- Prepare channels
  (recvC, multicastC, cOK) <- manyMulticast ?pid parties (f2p, p2f)
  let multicast x = do
        writeChan multicastC x 
        readChan cOK
  let recv = readChan recvC -- :: m (ACastMsg t)

  -- For sending ready just once
  sentReady <- newIORef False
  let sendReadyOnce v = do
        already <- readIORef sentReady
        if not already then do
          liftIO $ putStrLn $ "[" ++ ?pid ++ "] Sending READY"
          writeIORef sentReady True
          multicast $ ACast_READY v
        else return ()

  -- Sender provides input
  fork $ do
    mf <- readChan z2p
    case mf of
       ClockP2F_Pass -> ?pass
       ClockP2F_Through (ACastP2F_Input m) -> do
         liftIO $ putStrLn $ "Step 1"
         require (?pid == pidS) "[protACast]: only sender provides input"
         multicast (ACast_VAL m)
         liftIO $ putStrLn $ "[protACast]: multicast done"
         writeChan p2z ACastF2P_OK

  let n = length parties
  let thresh = ceiling (toRational (n+t+1) / 2)

  -- Receive messages from multicast
  fork $ forever $ do
    (pid', m) <- recv
    liftIO $ putStrLn $ "[protACast]: " ++ show (pid', m)
    case m of
      ACast_VAL v -> do
          -- Check this is the FIRST such message from the right sender
          require (pid' == pidS) "[protACast]: VAL(v) from wrong sender"
          readIORef inputReceived >>= \b -> require (not b) "[protACast]: Too many inputs received"
          writeIORef inputReceived True
          multicast $ ACast_ECHO v
          ?pass

      ACast_ECHO v -> do
          ech <- readIORef echoes
          let echV = Map.findWithDefault Map.empty v ech
          require (not $ Map.member pid' echV) $ "Already echoed"
          let echV' = Map.insert pid' () echV
          writeIORef echoes $ Map.insert v echV' ech
          liftIO $ putStrLn $ "[protACast] echo updated"
          --  Check if ready to decide
          --liftIO $ putStrLn $ "[protACast] " ++ show n ++ " " ++ show thresh ++ " " ++ show (Map.size echV')
          if Map.size echV' == thresh then do
              -- liftIO $ putStrLn "Threshold met! Sending ready"            
              sendReadyOnce v
          else do
              liftIO $ putStrLn $ "[protACast] not met yet"
              return ()
          liftIO $ putStrLn $ "[protACast] return OK"
          ?pass

      ACast_READY v -> do
          -- Check each signature
          rdy <- readIORef readys
          let rdyV = Map.findWithDefault Map.empty v rdy
          require (not $ Map.member pid' rdyV) $ "Already readyd"
          let rdyV' = Map.insert pid' () rdyV
          writeIORef readys $ Map.insert v rdyV' rdy
          liftIO $ putStrLn $ "[protACast] ready updated"

          dec <- readIORef decided
          if dec then ?pass
          else do
            let ct = Map.size rdyV'
            if ct == t+1 then do
              liftIO $ putStrLn $ "[protACast] deciding"
              sendReadyOnce v
              writeIORef decided True
              writeChan p2z (ACastF2P_Deliver v)
            else ?pass
  return ()


-- More utils

testEnvACastIdeal
  :: MonadEnvironment m =>
  Environment (ACastF2P String) (ClockP2F (ACastP2F String)) (SttCruptA2Z a (Either (ClockF2A String) Void)) (SttCruptZ2A b (Either ClockA2F Void)) Void (ClockZ2F) String m
testEnvACastIdeal z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    printEnvIdeal $ "[testEnvACastIdeal]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ClockP2F_Through $ ACastP2F_Input "I'm Alice")

  -- Empty the queue
  let checkQueue = do
        writeChan z2a $ SttCruptZ2A_A2F (Left ClockA2F_GetCount)
        mb <- readChan a2z
        let SttCruptA2Z_F2A (Left (ClockF2A_Count c)) = mb
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)

  () <- readChan pump
  whileM_ checkQueue $ do
    {- Two ways to make progress -}
    {- 1. Environment to Functionality - make progress -}
    -- writeChan z2f ClockZ2F_MakeProgress
    {- 2. Environment to Adversary - deliver the next message -}
    writeChan z2a $ SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))
    readChan pump

  writeChan outp "environment output: 1"

testACastBenign :: IO String
testACastBenign = runITMinIO 120 $ execUC testEnvACastIdeal (idealProtocol) (runAsyncF $ fACast) dummyAdversary


type Transcript = [Either
                         (SttCruptA2Z
                            (SID, MulticastF2P (ACastMsg String))
                            (Either
                               (ClockF2A (SID, ACastMsg String))
                               (SID, MulticastF2A (ACastMsg String))))
                         (PID, ACastF2P String)]

testEnvACast
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) (ClockP2F (ACastP2F String))
     (SttCruptA2Z (SID, MulticastF2P (ACastMsg String)) (Either (ClockF2A (SID,ACastMsg String)) (SID, MulticastF2A (ACastMsg String))))
     (SttCruptZ2A (ClockP2F (SID, ACastMsg String)) (Either ClockA2F (SID, MulticastA2F (ACastMsg String)))) Void
     (ClockZ2F) Transcript m
testEnvACast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

  transcript <- newIORef []
  
  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  clockChan <- newChan
  fork $ forever $ do
    mb <- readChan a2z
    modifyIORef transcript (++ [Left mb])
    case mb of
      SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
        printEnvReal $ "Pass"
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
        writeChan clockChan c
      SttCruptA2Z_P2A (pid, m) -> do
        case m of
          _ -> do
            printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
        ?pass
      _ -> error $ "Help!" ++ show mb


  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ClockP2F_Through $ ACastP2F_Input "I'm Alice")

  -- Empty the queue
  let checkQueue = do
        writeChan z2a $ SttCruptZ2A_A2F (Left ClockA2F_GetCount)
        c <- readChan clockChan
        -- printEnvReal $ "[testEnvACast]: Events remaining: " ++ show c
        return (c > 0)

  () <- readChan pump
  whileM_ checkQueue $ do
    writeChan z2a $ SttCruptZ2A_A2F (Left ClockA2F_GetCount)
    c <- readChan clockChan
    printEnvReal $ "[testEnvACast]: Events remaining: " ++ show c
    
    {- Two ways to make progress -}
    {- 1. Environment to Functionality - make progress -}
    -- writeChan z2f ClockZ2F_MakeProgress
    {- 2. Environment to Adversary - deliver first message -}
    idx <- getNbits 10
    let i = mod idx c
    writeChan z2a $ SttCruptZ2A_A2F (Left (ClockA2F_Deliver i))
    readChan pump

  -- Output is the transcript
  writeChan outp =<< readIORef transcript

testACastReal :: IO Transcript
testACastReal = runITMinIO 120 $ execUC
  testEnvACast 
  (runAsyncP protACast) 
  (runAsyncF $ bangFAsync fMulticast)
  dummyAdversary

{-- TODO: This is duplicated in MPC2.hs, fix it --}
makeSyncLog handler req = do
  ctr <- newIORef 0
  let syncLog = do
        -- Post the request
        log <- req
        -- Only process the new elements
        t <- readIORef ctr
        let tail = drop t log
        modifyIORef ctr (+ length tail)
        forM tail handler
        return ()
  return syncLog
  
{-- TODO: Simulator for ACast --}
simACast :: MonadAdversary m => Adversary (SttCruptZ2A (ClockP2F (SID, ACastMsg String))
                                                (Either (ClockA2F)
                                                        (SID, MulticastA2F (ACastMsg String))))
                                          (SttCruptA2Z (SID, MulticastF2P (ACastMsg String))
                                                (Either (ClockF2A  (SID, ACastMsg String))
                                                        (SID, MulticastF2A (ACastMsg String))))
                                          (ACastF2P String) (ClockP2F (ACastP2F String))
                                          (Either (ClockF2A String) Void) (Either ClockA2F Void) m
simACast (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
    -- Sender and set of parties is encoded in SID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid

  let isCruptSender = Map.member pidS ?crupt

  {--
   This is a full information simulator.
   This means that our strategy will be for the simulator to run a sandbox version of the real
      world protocol that's kept in the same configuration as the ideal world.
   The sandbox includes honest parties 
   The environment/dummyAdversary interface is routed directly to this virtualized execution.
   --}

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

  let sbxBullRand () = bangFAsync fMulticast

  -- Monitor the sandbox for outputs
  chanOK <- newChan
  partiesYet <- newIORef parties
  
  fork $ forever $ do
    mf <- readChan sbxp2z
    case mf of
      (_pidS, ACastF2P_OK) -> writeChan chanOK ()
      (pid, ACastF2P_Deliver _) -> do
        -- The sandbox produced output. We can deliver the corresponding message in fACast
        p <- readIORef partiesYet
        let Just idx = elemIndex pid p
        modifyIORef partiesYet $ delete pid
        liftIO $ putStrLn $ "delivering: " ++ pid
        writeChan a2f $ Left $ ClockA2F_Deliver idx

  let handleLeak m = do
         printAdv $ "handleLeak simulator"
         if isCruptSender then
           return ()
         else do
           -- The input is provided to the ideal functionality.
           -- We initiate the input operation in the sandbox.
           -- writeIORef fInputWaiting (Just x)
           writeChan sbxz2p (pidS, ClockP2F_Through $ ACastP2F_Input m)
           () <- readChan chanOK
           return ()

  -- Only process the new bulletin board entries since last time
  syncLeaks <- makeSyncLog handleLeak $ do
        writeChan a2f $ Left ClockA2F_GetLeaks
        mf <- readChan f2a
        let Left (ClockF2A_Leaks leaks) = mf
        return leaks

  let sbxProt () = protACast

  let sbxAdv (z2a',a2z') (p2a',a2p') (f2a',a2f') = do
        -- The sandbox adversary poses as the dummy adversary, but takes every
        -- activation opportunity to synchronize with the ideal world functionality
        fork $ forever $ do
          mf <- readChan z2a'
          printAdv $ show "Intercepted z2a'" ++ show mf
          syncLeaks
          printAdv $ "forwarding into to sandbox"
          case mf of
            SttCruptZ2A_A2F f -> writeChan a2f' f
            SttCruptZ2A_A2P pm -> writeChan a2p' pm
        fork $ forever $ do
          m <- readChan f2a'
          liftIO $ putStrLn $ show "f2a'" ++ show m
          writeChan a2z' $ SttCruptA2Z_F2A m
        fork $ forever $ do
          (pid,m) <- readChan p2a'
          liftIO $ putStrLn $ show "p2a'"
          writeChan a2z' $ SttCruptA2Z_P2A (pid, m)
        return ()

  -- We need to wait for the write token before we can finish initalizing the
  -- sandbox simulation.
  mf <- selectRead z2a f2a   -- TODO: could there be a P2A here?

  fork $ execUC_ sbxEnv (runAsyncP $ sbxProt ()) (runAsyncF (sbxBullRand ())) sbxAdv
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


testACastIdeal :: IO Transcript
testACastIdeal = runITMinIO 120 $ execUC
  testEnvACast 
  (idealProtocol) 
  (runAsyncF $ fACast)
  simACast


{--
 What are the options available to the environment?
 - Can choose to deliver messages in any order
 - Can choose to inject point-to-point messages to send from malicious parties
 - Can provide input to sender (if sender is honest)

 These choices could be adaptive and depend on the transcript observed so far,
 In this example, we'll only generate in a non-adaptive way, without looking at
 the content.
 --}

{-- Comparing transcripts
   Since the protocol and ideal functionalities are all determinsitic, we can
   only the environment makes random choices, hence for a fixed seed provided to
   the environment, we can check that these must be exactly the same in both worlds.
  --}

testCompare :: IO Bool
testCompare = runITMinIO 120 $ do
  liftIO $ putStrLn "*** RUNNING REAL WORLD ***"
  t1R <- runRandRecord $ execUC
             testEnvACast 
             (runAsyncP protACast) 
             (runAsyncF $ bangFAsync fMulticast)
             dummyAdversary
  let (t1, bits) = t1R
  liftIO $ putStrLn ""
  liftIO $ putStrLn ""  
  liftIO $ putStrLn "*** RUNNING IDEAL WORLD ***"
  t2 <- runRandReplay bits $ execUC
             testEnvACast 
             (idealProtocol) 
             (runAsyncF $ fACast)
             simACast
  return (t1 == t2)
