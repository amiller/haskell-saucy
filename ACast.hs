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
import qualified Data.Map.Strict as Map

{- fACast: an asynchronous broadcast functionality, Bracha's Broadcast -}
{-
   Narrative description:
   - Each party inputs a message (of type `a`, a parameter)
   - This functionality inlines an assumption on the fault tolerance
     TODO: Express `assume n>3t` as a generic functionality operator
   - If `a` 
 -}


data ACastP2F a = ACastP2F_Input a deriving Show
data ACastF2P a = ACastF2P_OK | ACastF2P_Deliver a deriving Show

--data ACastA2F a = ACastA2F_Deliver PID deriving Show

assertNothing Nothing = return ()
assertNothing _ = fail "Not nothing"

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
  require (pid == pidS) "Messages not from sender are ignored"

  -- Every honest party eventually outputs
  forMseq_ parties $ \pj -> do
    eventually $ writeChan f2p (pj, ACastF2P_Deliver m)

  writeChan f2p (pidS, ACastF2P_OK)



{- Protocol ACast -}

data ACastMsg t = ACast_VAL t | ACast_ECHO t | ACast_DECIDE t deriving (Show, Eq, Read)

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

protACast :: MonadProtocol m => Protocol (ACastP2F String) (ACastF2P String) (SID, MulticastF2P (ACastMsg String)) (SID, ACastMsg String) m
protACast (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid
  cOK <- newChan

  -- Keep track of state
  inputReceived <- newIORef False
  decided <- newIORef False
  echoes <- newIORef (Map.empty :: Map String (Map PID ()))
  
  -- Prepare channels
  (recvC, multicastC, cOK) <- manyMulticast ?pid parties (f2p, p2f)
  let multicast x = do
        writeChan multicastC x 
        readChan cOK
  let recv = readChan recvC -- :: m (ACastMsg t)

  -- Sender provides input
  fork $ do
    ACastP2F_Input m <- readChan z2p
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
          -- Check this is the *FIRST message from the right sender
          require (pid' == pidS) "[protACast]: VAL(v) from wrong sender"
          readIORef inputReceived >>= flip require "[protACast]: Too many inputs received" . not
          writeIORef inputReceived True

          multicast $ ACast_ECHO v
          writeChan p2z ACastF2P_OK

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
              liftIO $ putStrLn "Threshold met! Deciding"
              multicast $ ACast_DECIDE v
          else do
              liftIO $ putStrLn $ "[protACast] not met yet"
              return ()
          liftIO $ putStrLn $ "[protACast] return OK"
          writeChan p2z ACastF2P_OK

      ACast_DECIDE v -> do
          -- Check each signature
          dec <- readIORef decided
          if dec then writeChan p2z (ACastF2P_OK)
          else do
            ctr <- newIORef 0
            ct <- readIORef ctr
            if ct == thresh then do
              liftIO $ putStrLn "Deciding!"
              multicast $ ACast_DECIDE v
              writeIORef decided True
              writeChan p2z (ACastF2P_Deliver v)
            else 
              writeChan p2z ACastF2P_OK
  return ()


-- More utils

testEnvACast
  :: MonadEnvironment m =>
  Environment (ACastF2P String) (ACastP2F String) (SttCruptA2Z a (Either (ClockF2A String) Void)) (SttCruptZ2A b (Either ClockA2F Void)) Void (ClockZ2F) String m
testEnvACast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ACastP2F_Input "I'm Alice")

  -- Empty the queue
  let checkQueue = do
        writeChan z2a $ SttCruptZ2A_A2F (Left ClockA2F_GetCount)
        SttCruptA2Z_F2A (Left (ClockF2A_Count c)) <- readChan a2z
        liftIO $ putStrLn $ "Z[testEnvACast]: Events remaining: " ++ show c
        return (c > 0)

  () <- readChan pump
  whileM_ checkQueue $ do
    {- Two ways to make progress -}
    {- 1. Environment to Functionality - make progress -}
    -- writeChan z2f ClockZ2F_MakeProgress
    {- 2. Environment to Adversary - deliver first message -}
    writeChan z2a $ SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))
    readChan pump

  writeChan outp "environment output: 1"

testACastIdeal :: IO String
testACastIdeal = runITMinIO 120 $ execUC testEnvACast (idealProtocol) (runAsyncF $ fACast) dummyAdversary
{--
testACastReal :: IO String
testACastReal = runITMinIO 120 $ execUC
  testEnvACast 
  (protACast) 
  (runAsyncF $ bangFAsync fMulticast)
  dummyAdversary
--}
