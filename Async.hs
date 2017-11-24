 {-# LANGUAGE ImplicitParams, ScopedTypeVariables, MultiParamTypeClasses,
     Rank2Types
  #-} 


-- Asynchronous clocks
module Async where

import ProcessIO
import StaticCorruptions
import Duplex
import Leak
import Multisession

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map


{-- Program abstractions for asynchronous functionalities --}
{--
     "Asynchronous" network models allow the adversary to have full control 
   over the message delivery order.
     However, we are still interested in proving facts about when they are eventually delivered.

     We therefore use a round-based model for counting events. This model is expressed in SaUCy, as a programming abstraction:
        - getRound
        - byNextRound
        - withinNRounds

     As usual, these programming abstractions are defined as Haskell monad typeclasses, and are implemented as composition with another functionality (fClock).

     Looking ahead:
        Synchronous protocols are just ones where the parties have access to getRound
 --}

byNextRound m = do
  c <- ?registerCallback
  fork $ readChan c >> m
  return ()

withinNRounds :: (HasFork m, ?registerCallback :: m (Chan ())) => m () -> Integer -> m () -> m ()
withinNRounds _ 1 m = do
  c <- ?registerCallback
  fork $ readChan c >> m
  return ()
withinNRounds def n m = do
  assert (n >= 1) "withinNRounds must be called with n >= 1"
  c <- ?registerCallback
  fork $ readChan c >> withinNRounds def (n-1) m >> def
  return ()



{-- The Asynchronous Clock functionality --}
{--
  fClock functionality:
   Lets other functionalities schedule events to be delivered in the future, in any order chosen by the adversary
   However, it keeps track of the current round
   Environment can "force" progress to move along
   The adversary is thus unable to stall forever
 --}
    
type CallbackID = Int
type Round = Int

{-- Types of messages exchanged with the clock --}
data ClockA2F = ClockA2F_GetState | ClockA2F_Deliver Int Int deriving Show
data ClockF2A = ClockF2A_RoundOK PID | ClockF2A_State Int (Map PID Bool) deriving Show
data ClockF2Z = ClockF2Z_Round Int deriving Show
data ClockZ2F = ClockZ2F_MakeProgress deriving Show
data ClockPeerIn = ClockPeerIn_Register deriving Show
data ClockPeerOut = ClockPeerOut_Registered CallbackID | ClockPeerOut_Callback CallbackID deriving Show

fClock crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do

  -- Store state for the clock
  buffer <- newIORef (empty :: Map Round [CallbackID]) -- map of round/callbacks to deliver
  cbCounter <- newIORef (0 :: CallbackID)
  round <- newIORef (0 :: Round)

  -- Adversary can query the current state, and deliver messages early
  fork $ forever $ do
    mf <- readChan a2f
    case mf of 
      --ClockA2F_GetState -> do
      --               r <- readIORef round
      --               buf <- readIORef buffer
      --               writeChan f2a $ ClockF2A_State r buf
      ClockA2F_Deliver r idx -> do
                     buf <- readIORef buffer
                     let rbuf :: [CallbackID] = Map.findWithDefault [] r buf
                     let callback = rbuf !! idx
                     let rbuf' = deleteAtIndex idx rbuf
                     writeIORef buffer (Map.insert r rbuf' buf)
                     ?duplexWrite $ ClockPeerOut_Callback callback

  -- Functionality on other side of duplex can register callbacks for the next round
  fork $ forever $ do
    ClockPeerIn_Register <- ?duplexRead
    cbid <- readIORef cbCounter
    writeIORef cbCounter (cbid+1)
    r <- readIORef round
    buf <- readIORef buffer
    let rbuf = Map.findWithDefault [] (r+1) buf
    let rbuf' = rbuf ++ [cbid]
    writeIORef buffer (Map.insert (r+1) rbuf' buf )
    ?duplexWrite $ ClockPeerOut_Registered cbid
                                 
  -- Allow the environment to force progress along
  fork $ forever $ do
    ClockZ2F_MakeProgress <- readChan z2f
    liftIO $ putStrLn $ "[fAsync] MakeProgress"
    r <- readIORef round
    buf <- readIORef buffer
    let rbuf = Map.findWithDefault [] r buf
    liftIO $ putStrLn $ "[fAsync]" ++ show buf
    if length rbuf > 0 then do
        -- Deliver the first message, remove it from buffer
        let cb = rbuf !! 0
        writeIORef buffer $ Map.insert r (drop 1 rbuf) buf
        liftIO $ putStrLn $ "[fAsync] sending callback"
        ?duplexWrite $ ClockPeerOut_Callback cb
    else do
        -- Advance the round
        writeIORef buffer $ Map.delete r buf
        writeIORef round $ (r+1)
        liftIO $ putStrLn $ "[fAsync] round over"
        writeChan f2z $ ClockF2Z_Round (r+1)
  return ()





{-- Implementation of MonadAsync --}
{--
  Our model of asynchronous protocols is built around an idealized "clock" functionality, fClock
 --}

--instance {-# OVERLAPS #-} (MonadReader (Chan (Chan ())) m, MonadDuplex ClockPeerIn ClockPeerOut m) => MonadAsync m where
--    registerCallback = do
--      reg :: Chan (Chan ()) <- ask
--      duplexWrite ClockPeerIn_Register
--      cb <- readChan reg
--      return cb

_runAsyncF :: (HasFork m, ?duplexWrite::ClockPeerIn -> m (),
            ?duplexRead::m ClockPeerOut) =>
          ((?registerCallback :: m (Chan ())) => p -> (a2, b1) -> (a3, b2) -> (Chan a4, Chan a5) -> m b3)
               -> p -> (a2, b1) -> (a3, b2) -> (a6, b4) -> m b3
_runAsyncF f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  callbacks <- newIORef empty
  reg <- newChan
  -- Create a new thread to handle callbacks
  fork $ forever $ do
    mf <- ?duplexRead
    case mf of
      ClockPeerOut_Registered cb -> do
                     liftIO $ putStrLn $ "[_runAsyncF] creating callback" ++ show cb
                     chan <- newChan
                     modifyIORef callbacks (Map.insert cb chan)
                     writeChan reg chan
      ClockPeerOut_Callback cb -> do
                     -- Activate the callback
                     liftIO $ putStrLn $ "[_runAsyncF] Triggering callback" ++ show cb
                     cbMap <- readIORef callbacks
                     let chan = (\(Just c)->c) $ Map.lookup cb cbMap
                     writeChan chan ()

  z2f' <- newChan
  f2z' <- newChan
  let ?registerCallback = do
        ?duplexWrite ClockPeerIn_Register
        cb <- readChan reg
        return cb
    in f crupt (p2f, f2p) (a2f, f2a) (z2f', f2z')


runAsyncF :: (HasFork m, (?sid::SID)) =>
     ((?sid::SID, ?registerCallback:: m (Chan ())) => Map PID ()
      -> (Chan (PID, t3), Chan (PID, b))
      -> (Chan a2f, Chan f2a)
      -> (Chan z2f, Chan f2z)
      -> m ())
     -> Map PID ()
     -> (Chan (PID, DuplexP2F Void t3), Chan (PID, DuplexF2P Void b))
     -> (Chan (DuplexA2F ClockA2F a2f), Chan (DuplexF2A ClockF2A f2a))
     -> (Chan (DuplexZ2F ClockZ2F z2f), Chan (DuplexF2Z ClockF2Z f2z))
     -> m ()
runAsyncF f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  runDuplexF fClock (_runAsyncF f) crupt (p2f, f2p) (a2f, f2a) (z2f, f2z)


runAsyncP :: (HasFork m, (?sid::SID)) =>
     (PID -> (Chan z2p, Chan p2z) -> (Chan f2p, Chan p2f) -> m ())
     -> PID
     -> (Chan z2p, Chan p2z)
     -> (Chan (DuplexF2P Void f2p), Chan (DuplexP2F Void p2f))
     -> m ()
runAsyncP p pid (z2p, p2z) (f2p, p2f) = do
  -- Asynchronous clock is transparent to parties
  p2f' <- wrapWrite DuplexP2F_Right          p2f
  f2p' <- wrapRead (\(DuplexF2P_Right m)->m) f2p

  sid <- getSID
  let (leftConf :: String, rightConf :: String) = readNote ("runDuplexF:" ++ show (snd sid)) $ snd sid
  let rightSID = extendSID sid "DuplexRight" rightConf
  fork $ runSID rightSID $ p pid (z2p, p2z) (f2p', p2f')
  return ()

{-
-- Example: fAuth
      fAuth is an asynchronous, one-shot, authenticated communication channel.
      The PIDs of the Sender and Receiver are encoded in the SID
      The sender can set the message (once). 
      After one (asynchronous) round, the receiver receives the message

-}

data FAuthF2P a = FAuthF2P_OK | FAuthF2P_Deliver a deriving (Eq, Read, Show)

fAuth :: (HasFork m, ?sid::SID, ?leak::a -> m (), ?registerCallback::m (Chan ())) =>
     Map PID ()
     -> (Chan (PID, a), Chan (PID, FAuthF2P a))
     -> (Chan Void, Chan Void) 
     -> (Chan Void, Chan Void)
     -> m ()
fAuth crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Parse SID as sender, recipient, ssid
  sid <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: String) = readNote "fAuth" $ snd sid 

  -- Store an optional message
  recorded <- newIORef False

  fork $ forever $ do
    (pid, m) <- readChan p2f
    liftIO $ putStrLn $ "[fAuth sid]: " ++ show sid
    liftIO $ putStrLn $ "[fAuth] message received" ++ show (pidS, pidR, ssid)

    -- Sender can only send message once
    False <- readIORef recorded
    if not (pid == pidS) then fail "Invalid sender to fAuth" 
    else do
      writeIORef recorded True
      liftIO $ putStrLn $ "fAuth: notifying adv"
      ?leak m
      byNextRound $ writeChan f2p (pidR, FAuthF2P_Deliver m)
    writeChan f2p (pidS, FAuthF2P_OK)

  return ()

{-- Example environment using fAuth --}

testEnvAuthAsync z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestAuthAsync", show ("", show ("", show ("Alice", "Bob", ""))))
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    ?pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show (m :: (SttCruptA2Z
                           (DuplexF2P Void (DuplexF2P Void (FAuthF2P String)))
                           (DuplexF2A ClockF2A (DuplexF2A (LeakF2A String) Void))))
    ?pass
  fork $ forever $ do
    DuplexF2Z_Left f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show f
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", DuplexP2F_Right "hi Bob")

  -- Let the adversary see
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Right $ DuplexA2F_Left $ LeakA2F_Get

  -- Advance to round 1
  () <- readChan pump
  writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  -- Advance to round 2
  () <- readChan pump
  writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  () <- readChan pump 
  writeChan outp "environment output: 1"

testAuthAsync :: IO String
testAuthAsync = runRand $ execUC testEnvAuthAsync (runAsyncP idealProtocol) (runAsyncF $ runLeakF fAuth) dummyAdversary


{--


{-- Example environments using !fAuth --}

instance (MonadAsync m => MonadAsync (SIDMonadT m)) where
    registerCallback = lift registerCallback

--instance (MonadLeak (SID, a) m => MonadLeak a (SIDMonadT m)) where
--    leak x = do
--      sid <- getSID
--      lift (leak (sid, x))

testEnvBangAsync z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestAuthAsync", show ("", (show ("", ""))))
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
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
  --
  --let voidLeft sid = ("", show (voidSID, sid))
  --let sid' = voidLeft $ voidLeft $ ("ssidX", show ("Alice","Bob",""))
  writeChan z2p ("Alice", (("ssidX", show ("Alice","Bob","")), "hi Bob"))

  -- Let the adversary read the buffer
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Right $ DuplexA2F_Left $ LeakA2F_Get

  -- Advance to round 1
  -- Deliver 0
  () <- readChan pump
  writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  -- Deliver 1
  () <- readChan pump
  writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  () <- readChan pump 
  writeChan outp "environment output: 1"


testBangAsync :: IO String
testBangAsync = runRand $ execUC testEnvBangAsync (runAsyncP $ runLeakP idealProtocol) (runAsyncF $ runLeakF $ bangF fAuth) dummyAdversary


-- TODO: A modular simulator
--runClockS s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
--  runDuplexS dummyAdversary s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f)



-}
