 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances
  
  #-} 


-- Asynchronous clocks
module Async where

import ProcessIO
import StaticCorruptions
import Duplex
import Leak

import Control.Concurrent.MonadIO
import Control.Monad (forever)
import Control.Monad.State
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map
    
type CallbackID = Int
type Round = Int

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
                     duplexWrite $ ClockPeerOut_Callback callback

  -- Functionality on other side of duplex can register callbacks for the next round
  fork $ forever $ do
    ClockPeerIn_Register <- duplexRead
    cbid <- readIORef cbCounter
    writeIORef cbCounter (cbid+1)
    r <- readIORef round
    buf <- readIORef buffer
    let rbuf = Map.findWithDefault [] (r+1) buf
    let rbuf' = rbuf ++ [cbid]
    writeIORef buffer (Map.insert (r+1) rbuf' buf )
    duplexWrite $ ClockPeerOut_Registered cbid
                                 
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
        duplexWrite $ ClockPeerOut_Callback cb
    else do
        -- Advance the round
        writeIORef buffer $ Map.delete r buf
        writeIORef round $ (r+1)
        liftIO $ putStrLn $ "[fAsync] round over"
        writeChan f2z $ ClockF2Z_Round (r+1)
  return ()


class HasFork m => MonadAsync m where
    registerCallback :: m (Chan ())

type AsyncFuncT = ReaderT (Chan (Chan ()))

instance MonadSID m => MonadSID (AsyncFuncT m) where
    getSID = lift getSID

instance MonadDuplex ClockPeerIn ClockPeerOut m => MonadAsync (AsyncFuncT m) where
    registerCallback = do
      reg :: Chan (Chan ()) <- ask
      lift $ duplexWrite ClockPeerIn_Register
      cb <- readChan reg
      return cb

_runAsyncF f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  callbacks <- newIORef empty
  reg <- newChan
  -- Create a new thread to handle callbacks
  fork $ forever $ do
    mf <- duplexRead
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
  runReaderT (f crupt (p2f, f2p) (a2f, f2a) (z2f', f2z')) reg

runAsyncF :: (HasFork m, MonadSID m) =>
     (Map PID ()
      -> (Chan (t2, t3), Chan (t, b))
      -> (Chan a2f, Chan f2a)
      -> (Chan a4, Chan a5)
      -> AsyncFuncT (DuplexT ClockPeerIn ClockPeerOut m) ())
     -> Map PID ()
     -> (Chan (t2, DuplexP2F t1 t3), Chan (t, DuplexF2P () b))
     -> (Chan (DuplexA2F ClockA2F a2f), Chan (DuplexF2A ClockF2A f2a))
     -> (Chan (DuplexZ2F ClockZ2F z2f), Chan (DuplexF2Z ClockF2Z f2z))
     -> m ()
runAsyncF f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  runDuplexF fClock (_runAsyncF f) crupt (p2f, f2p) (a2f, f2a) (z2f, f2z)

runAsyncP p crupt (z2p, p2z) (f2p, p2f) = do
  -- Asynchronous clock is transparent to parties
  p2f' <- wrapWrite DuplexP2F_Right          p2f
  f2p' <- wrapRead (\(DuplexF2P_Right m)->m) f2p
  p crupt (z2p, p2z) (f2p', p2f')

-- TODO
--runClockS s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
--  runDuplexS dummyAdversary s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f)

{-
-- Example: fAuth
      fAuth is an asynchronous, one-shot, authenticated communication channel.
      The PIDs of the Sender and Receiver are encoded in the SID
      The sender can set the message (once). 
      After one (asynchronous) round, the receiver receives the message

-}

data FAuthF2P a = FAuthF2P_OK | FAuthF2P_Deliver a deriving (Eq, Read, Show)

fAuth crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Parse SID as sender, recipient, ssid
  sid <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: String) = read $ snd sid

  -- Store an optional message
  recorded <- newIORef False

  fork $ forever $ do
    (pid, m :: String) <- readChan p2f
    liftIO $ putStrLn $ "[fAuth] message received" ++ show (pidS, pidR, ssid)

    -- Sender can only send message once
    False <- readIORef recorded
    if not (pid == pidS) then fail "Invalid sender to fAuth" 
    else do
      writeIORef recorded True
      liftIO $ putStrLn $ "fAuth: notifying adv"
      leak (pid, m)
      cb <- registerCallback
      fork $ do
           readChan cb
           writeChan f2p (pidR, FAuthF2P_Deliver m)
    writeChan f2p (pidS, FAuthF2P_OK)

  return ()

{-- Example environment using fAuth --}

testEnvAuthAsync z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestAuthAsync", show ("Alice", "Bob", ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show (m :: (SttCruptA2Z
                           (DuplexF2P () (DuplexF2P () (FAuthF2P String)))
                           (DuplexF2A ClockF2A (DuplexF2A (LeakF2A (PID,String)) ()))))
    pass
  fork $ forever $ do
    DuplexF2Z_Left f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show f
    pass

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

instance MonadAsync m => MonadAsync (LeakFuncT a m) where
    registerCallback = lift registerCallback

testAuthAsync :: IO String
testAuthAsync = runRand $ execUC testEnvAuthAsync (runAsyncP idealProtocol) (runAsyncF (runLeakF fAuth)) dummyAdversary

{-
testEnvDumb z2exec (p2z, z2p) (a2z, z2a) pump outp = do
  -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("sidTestBangBangSync","") empty

  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    --writeChan outp ()
    pass

  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m
    --writeChan outp "environment output: 1"
    pass

  () <- readChan pump 
  writeChan outp "environment output: 1"
-}

-- Identities:
--  runClockP idealProtocol  ~= idealProtocol
--  runClockS dummyAdvesrary ~= dummyAdversary

--testSquashBangIdeal :: IO String
--testSquashBangIdeal = runRand $ execUC testEnvSquashBangSync idealProtocol (runClockF $ bangF $ bangF $ fSync) (runClockS squashS)

--testSquashBangReal :: IO String
--testSquashBangReal = runRand $ execUC testEnvSquashBangSync (runClockP squash) (runClockF $ bangF $ fSync) dummyAdversary
{-
{-- This is a silly test, but it serves as a sanity check. We can apply the runClockF
    operator in any order. runClockF(_) is a well formed functionality.  --}
testSquashBangReal' :: IO String
testSquashBangReal' = runRand $ execUC testEnvBBSSync squash (bangF $ runClockF $ fSync) dummyAdversary

testSquashBangIdeal' :: IO String
testSquashBangIdeal' = runRand $ execUC testEnvBBSSync idealProtocol (bangF $ bangF $ runClockF $ fSync) squashS
-}
