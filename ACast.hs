 {-# LANGUAGE ScopedTypeVariables, MultiParamTypeClasses, ImplicitParams
  #-} 

module ACast where

import ProcessIO
import StaticCorruptions
import Both
import Duplex
import Leak
import Async
import Multisession
import Multicast
import Signature
import Safe

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)

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

fACast :: (HasFork m, ?leak::a -> m (), ?registerCallback::m (Chan ()), ?sid::SID) =>
     Crupt
     -> (Chan (PID, ACastP2F a), Chan (PID, ACastF2P a))
     -> (Chan Void, Chan (ACastF2A a))
     -> (Chan Void, Chan Void)
     -> m ()
fACast crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender, set of parties, and tolerance parameter is encoded in SID
  sid <- getSID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "fACast" $ snd sid

  -- Check the fault tolerance parameters
  let n = length parties
  assert (Map.size crupt <= t) "Fault tolerance assumption violated"
  assert (3*t < n) "Invalid fault tolerance parameter (must be 3t<n)"

  -- Store the first sent value
  value <- newIORef (Nothing :: Maybe a)

  -- Allow sender to choose the input
  fork $ forever $ do
    (pid, ACastP2F_Input m) <- readChan p2f
    liftIO $ putStrLn $ "[fACast]: input read " -- ++ show m
    assert (pid == pidS) "Messages not from sender are ignored"
    readIORef value >>= assertNothing
    writeIORef value (Just m)        

    -- Every honest party outputs within 2 rounds
    forMseq_ parties $ \pid' -> do
        withinNRounds (writeChan f2a ACastF2A_Advance) 2 $ do
           writeChan f2p (pid', ACastF2P_Deliver m)
    writeChan f2p (pidS, ACastF2P_OK)

  return ()





{- Protocol ACast -}

data ACastMsg t = ACast_VAL t | ACast_ECHO (SignatureSig, t) | ACast_DECIDE t [Maybe SignatureSig] deriving (Show, Eq, Read)

-- Give (fBang fMulticast) a nicer interface
manyMulticast :: (HasFork m) =>
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
                     assert (pidS == pid) "ok delivered to wrong pid"
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

protACast :: (HasFork m, ?sid:SID) =>
     PID
     -> (Chan (ACastP2F String), Chan (ACastF2P String))
     -> (Chan (BothF2P (SID, MulticastF2P (ACastMsg String)) (SID, SignatureF2P)),
         Chan (BothP2F (SID, ACastMsg String) (SID, SignatureP2F String)))
     -> m ()
protACast pid (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  sid <- getSID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd sid
  cOK <- newChan

  -- Keep track of state
  inputReceived <- newIORef False
  decided <- newIORef False
  echoes <- newIORef (Map.empty :: Map String (Map PID SignatureSig))
  
  -- Prepare channels
  ((f2p_mcast, p2f_mcast), (f2p_sig, p2f_sig)) <- splitBothP (f2p, p2f)
  --(f2p_mcast, p2f_mcast) <- return (f2p, p2f)
  (recvC, multicastC, cOK) <- manyMulticast pid parties (f2p_mcast, p2f_mcast)
  let multicast x = do
        writeChan multicastC x 
        readChan cOK
  let recv = readChan recvC -- :: m (ACastMsg t)

  -- Sender provides input
  fork $ do
    ACastP2F_Input m <- readChan z2p
    liftIO $ putStrLn $ "Step 1"
    assert (pid == pidS) "[protACast]: only sender provides input"
    multicast (ACast_VAL m)
    liftIO $ putStrLn $ "[protACast]: multicast done"
    writeChan p2z ACastF2P_OK

  let sign v = do
        writeChan p2f_sig $ (("", show (pid, "")), SignatureP2F_Sign v)
        (_, SignatureF2P_Sig sig) <- readChan f2p_sig
        return sig

  let verify pid msg sig = do
        writeChan p2f_sig $ (("", show (pid, "")), SignatureP2F_Verify msg sig)
        (_, SignatureF2P_Verify b) <- readChan f2p_sig
        return b

  let n = length parties
  let thresh = ceiling (toRational (n+t+1) / 2)

  -- Receive messages from multicast
  fork $ forever $ do
    (pid', m) <- recv
    liftIO $ putStrLn $ "[protACast]: " ++ show (pid', m)
    case m of
      ACast_VAL v -> do
          -- Check this is the *FIRST message from the right sender
          assert (pid' == pidS) "[protACast]: VAL(v) from wrong sender"
          readIORef inputReceived >>= flip assert "[protACast]: Too many inputs received" . not
          writeIORef inputReceived True

          -- Create a signature
          sig <- sign v
          -- Multicast ECHO(sig, v)
          multicast $ ACast_ECHO (sig, v)
          writeChan p2z ACastF2P_OK

      ACast_ECHO (sig, v) -> do
          -- Check the signature using the fSignature instance for pidS'
          -- Add this signature to a list
          b <- verify pidS v sig
          assert b "[protACast]: verify sig failed"
          ech <- readIORef echoes
          let echV = Map.findWithDefault Map.empty v ech
          assert (not $ Map.member pid' echV) $ "Already echoed"
          let echV' = Map.insert pid' sig echV
          writeIORef echoes $ Map.insert v echV' ech
          liftIO $ putStrLn $ "[protACast] echo updated"
          --  Check if ready to decide
          --liftIO $ putStrLn $ "[protACast] " ++ show n ++ " " ++ show thresh ++ " " ++ show (Map.size echV')
          if Map.size echV' == thresh then do
              liftIO $ putStrLn "Threshold met! Deciding"
              multicast $ ACast_DECIDE v [Map.lookup p echV' | p <- parties]
          else do
              liftIO $ putStrLn $ "[protACast] not met yet"
              return ()
          liftIO $ putStrLn $ "[protACast] return OK"
          writeChan p2z ACastF2P_OK

      ACast_DECIDE v sigs -> do
          -- Check each signature
          dec <- readIORef decided
          if dec then writeChan p2z (ACastF2P_OK)
          else do
            ctr <- newIORef 0
            forMseq_ (zip parties sigs) $ \(p, sig') ->
                case sig' of 
                  Nothing -> return ()
                  Just sig -> verify p v sig >>= \b -> 
                              if b then modifyIORef ctr (+1)
                              else return ()
            ct <- readIORef ctr
            if ct == thresh then do
              liftIO $ putStrLn "Deciding!"
              multicast $ ACast_DECIDE v sigs
              writeIORef decided True
              writeChan p2z (ACastF2P_Deliver v)
            else 
              writeChan p2z ACastF2P_OK
  return ()


-- More utils

splitBothP (f2p, p2f) = do
  -- Reading
  f2pL <- newChan
  f2pR <- newChan
  fork $ forever $ do
    mf <- readChan f2p
    case mf of
      BothF2P_Left  m -> writeChan f2pL m 
      BothF2P_Right m -> writeChan f2pR m

  -- Writing
  p2fL <- wrapWrite BothP2F_Left  p2f
  p2fR <- wrapWrite BothP2F_Right p2f

  return ((f2pL, p2fL), (f2pR, p2fR))



testEnvACast
  :: (MonadDefault m) =>
     Chan SttCrupt_SidCrupt
     -> (Chan (PID, ACastF2P String), Chan (PID, ACastP2F String))
     -> (Chan a, Chan b)
     -> (Chan (DuplexF2Z ClockF2Z voidA),
         Chan (DuplexZ2F ClockZ2F voidB))
     -> Chan ()
     -> Chan [Char]
     -> m ()
testEnvACast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestACast", extendRight $ extendRight $ show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
    pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " -- ++ show m 
    pass
  fork $ forever $ do
    DuplexF2Z_Left f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show f
    pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ACastP2F_Input "I'm Alice")

  -- Advance to round 1
  forMseq_ [1..58 :: Integer] $ const $ do
                 () <- readChan pump
                 --liftIO $ putStrLn "[testEnvACast]: read pump"
                 writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  () <- readChan pump 
  writeChan outp "environment output: 1"

testACastIdeal :: IO String
testACastIdeal = runRand $ execUC testEnvACast (runAsyncP $ runLeakP idealProtocol) (runAsyncF $ runLeakF $ fACast) voidAdversary

testACastReal :: IO String
testACastReal = runRand $ execUC 
  testEnvACast 
  (runAsyncP $ runLeakP $ protACast) 
  (runAsyncF $ runLeakF $ alterSIDF (\(tag,conf) -> (tag, show ("",""))) $ 
                 runBothF
                 (bangF fMulticast)
                 (bangF $ fSignature defaultSignature))
  dummyAdversary
