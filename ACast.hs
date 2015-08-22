 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses
  #-} 

module ACast where

import ProcessIO
import StaticCorruptions
import Duplex
import Leak
import Async
import Multisession
import Multicast
import Signature

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.State
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

{- fACast: an asynchronous broadcast functionality -}
{-
   Narrative description:
   - Each party inputs a message (of type `a`, a parameter)
   - This functionality inlines an assumption on the fault tolerance
     TODO: Express `assume n>3t` as a generic functionality operator
   - If `a`
 -}

data ACastP2F a = ACastP2F_Input a deriving Show
data ACastF2P a = ACastF2P_OK | ACastF2P_Deliver a deriving Show
data ACastF2A a = ACastF2A_Advance deriving Show
--data ACastA2F a = ACastA2F_Deliver PID deriving Show

assertNothing Nothing = return ()
assertNothing _ = fail "Not nothing"

fACast :: (MonadSID m, MonadLeak a m, MonadAsync m, Show a) =>
     Crupt
     -> (Chan (PID, ACastP2F a), Chan (PID, ACastF2P a))
     -> (Chan Void, Chan (ACastF2A a))
     -> (Chan Void, Chan Void)
     -> m ()
fACast crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender, set of parties, and tolerance parameter is encoded in SID
  sid <- getSID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = read $ snd sid

  -- Check the fault tolerance parameters
  let n = length parties
  assert (Map.size crupt <= t) "Fault tolerance assumption violated"
  assert (n > 3*t) "Invalid fault tolerance parameter (must be 3t<n)"

  -- Store the first sent value
  value <- newIORef (Nothing :: Maybe a)

  -- Allow sender to choose the input
  fork $ forever $ do
    (pid, ACastP2F_Input m) <- readChan p2f
    liftIO $ putStrLn $ "[fACast]: input read " ++ show m
    assert (pid == pidS) "Messages not from sender are ignored"
    readIORef value >>= assertNothing
    writeIORef value (Just m)        

    -- Every honest party outputs within 2 rounds
    forM_ parties $ \pid' -> do
        withinNRounds (writeChan f2a ACastF2A_Advance) 2 $ do
           writeChan f2p (pid', ACastF2P_Deliver m)
    writeChan f2p (pidS, ACastF2P_OK)

  return ()





{- Protocol ACast -}

data ACastMsg t = ACast_VAL t | ACast_ECHO (SignatureSig, t) | ACast_DECIDE ([Maybe SignatureSig], t)

-- Give (fBang fMulticast) a nicer interface
manyMulticast :: (HasFork m) =>
     PID -> [PID]
     -> (Chan (SID, (MulticastF2P t)), Chan (SID, t))
     -> m (Chan (PID, t), Chan t)
manyMulticast pid parties (f2p, p2f) = do
  p2f' <- newChan
  f2p' <- newChan
  cOK <- newChan

  -- Handle writing
  fork $ forever $ do
    forM_  [0..] $ \(ctr :: Integer) -> do
       m <-readChan p2f'
       let ssid = (show ctr, show (pid, parties, ""))
       writeChan p2f (ssid, m)
       readChan cOK

  -- Handle reading (messages delivered in any order)
  fork $ forever $ do
    (ssid, mf) <- readChan f2p
    let (pidS :: PID, _ :: [PID], _ :: String) = read $ snd ssid
    case mf of
      MulticastF2P_OK -> do
                     assert (pidS == pid) "ok delivered to wrong pid"
                     writeChan cOK ()
      MulticastF2P_Deliver m -> do
                     writeChan f2p' (pid, m)
  return (f2p', p2f')

readBangMulticast pid parties f2p = do
  c <- newChan
  fork $ forever $ do
    forM_ [0..] 

writeBangSequential p2f = do
  c <- newChan
  fork $ do
    forM_  [0..] $ \(ctr :: Integer) -> do
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

protACast :: (MonadSID m, HasFork m) =>
     PID
     -> (Chan (ACastP2F String), Chan (ACastF2P String))
     -> (Chan (DuplexF2P (SID, MulticastF2P (ACastMsg String)) (SignatureF2P String)),
         Chan (DuplexP2F (SID, ACastMsg String) (SignatureP2F String)))
     -> m ()
protACast pid (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  sid <- getSID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = read $ snd sid

  cOK <- newChan

  -- Keep trac
  inputReceived <- newIORef False
  echoes <- newIORef (Map.empty :: Map PID (SignatureSig, v))

  -- Sender provides input
  fork $ do
    ACastP2F_Input m <- readChan z2p
    assert (pid == pidS) "[protACast]: only sender provides input"
    --multicast m

  -- Prepare channels
  ((f2p_mcast, p2f_mcast), (f2p_sig, p2f_sig)) <- splitDuplexP (f2p, p2f)
  (recvC, multicastC) <- manyMulticast pid parties (f2p_mcast, p2f_mcast)
  let multicast x = writeChan multicastC x
  let recv = readChan recvC -- :: m (ACastMsg t)

  -- Receive messages from multicast
  fork $ forever $ do
    (pid', m) <- recv
    case m of
      ACast_VAL v -> do
          -- Check this is the *FIRST message from the right sender
          assert (pid' == pidS) "[protACast]: VAL(v) from wrong sender"
          readIORef inputReceived >>= flip assert "[protACast]: Too many inputs received" . not
          writeIORef inputReceived True

          -- Create a signature
          sig <- undefined
          -- Multicast ECHO(sig, v)
          multicast $ ACast_ECHO (sig, v)

      ACast_ECHO (sig, v) -> 
          -- Check the signature using the fSignature instance for pidS'
          --  verifySig pidS' sig v
          -- Add this signature to a list
          undefined
      ACast_DECIDE (sigs, v) -> 
          -- Check each signature
          undefined
    
  return ()


-- More utils

splitDuplexP (f2p, p2f) = do
  -- Reading
  f2pL <- newChan
  f2pR <- newChan
  fork $ forever $ do
    mf <- readChan f2p
    case mf of
      DuplexF2P_Left  m -> writeChan f2pL m 
      DuplexF2P_Right m -> writeChan f2pR m

  -- Writing
  p2fL <- wrapWrite DuplexP2F_Left  p2f
  p2fR <- wrapWrite DuplexP2F_Right p2f

  return ((f2pL, p2fL), (f2pR, p2fR))


testEnvACast
  :: (MonadDefault m) =>
     Chan SttCrupt_SidCrupt
     -> (Chan (PID, ACastF2P String), Chan (PID, ACastP2F String))
     -> (Chan Void, Chan Void)
     -> (Chan (DuplexF2Z ClockF2Z (DuplexF2Z Void Void)), 
         Chan (DuplexZ2F ClockZ2F (DuplexZ2F Void Void)))
     -> Chan ()
     -> Chan [Char]
     -> m ()
testEnvACast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
    pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m 
    pass
  fork $ forever $ do
    DuplexF2Z_Left f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show f
    pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ACastP2F_Input "I'm Alice")

  -- Advance to round 1
  forM_ [1..12 :: Integer] $ const $ do
                 () <- readChan pump
                 --liftIO $ putStrLn "[testEnvACast]: read pump"
                 writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  () <- readChan pump 
  writeChan outp "environment output: 1"

testACastIdeal :: IO String
testACastIdeal = runRand $ execUC testEnvACast (runAsyncP $ runLeakP idealProtocol) (runAsyncF $ runLeakF $ fACast) voidAdversary

--testACastReal :: IO String
--testACastReal = runRand $ execUC undefined (runAsyncP $ runLeakP protACast) (runAsyncF $ runLeakF $ runDuplexF (bangF fMulticast) (fSignature (undefined, undefined, undefined))) dummyAdversary
