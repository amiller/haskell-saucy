{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds
  #-} 


-- Asynchronous clocks
module Async where

import ProcessIO
import StaticCorruptions
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

   This is captured by extending the Functionality syntax with
   "eventually" blocks. The expression `eventually m` registers
   the action `m` to be delivered later.

   m is a monad action, `eventually` returns nothing. The type is
      eventually :: MonadFunctionality m => m a -> m ()`
 --}


type MonadFunctionalityAsync m = (MonadFunctionality m,
                                  ?eventually :: m () -> m ())

eventually :: MonadFunctionalityAsync m => m () -> m ()
eventually m = ?eventually m

{-- The Asynchronous functionality wrapper --}
{--
   Lets other functionalities schedule events to be delivered in the future, in any order chosen by the adversary.
   Environment can "force" progress to move along, thus the adversary is thus unable to stall forever.
 --}
    
type CallbackID = Int
type Round = Int

{-- Types of messages exchanged with the clock --}
data ClockA2F = ClockA2F_GetCount | ClockA2F_Deliver Int deriving Show
data ClockF2A = ClockF2A_Count Int deriving Show
data ClockZ2F = ClockZ2F_MakeProgress deriving Show
data ClockF2Z

{-- Implementation of MonadAsync --}

runAsyncF :: MonadFunctionality m =>
             (MonadFunctionalityAsync m => Functionality p2f f2p a2f f2a z2f f2z m)
          -> Functionality p2f f2p (Either ClockA2F a2f) (Either ClockF2A f2a) (Either ClockZ2F z2f) (Either ClockF2Z f2z) m

runAsyncF f (p2f, f2p) (a2f, f2a) (z2f, f2z) = do

  -- Store state for the clock
  runqueue <- newIORef []

  a2f' <- newChan
  f2a' <- wrapWrite Right f2a 

  -- Adversary can query the current state, and deliver messages early
  fork $ forever $ do
    mf <- readChan a2f
    case mf of
      Left ClockA2F_GetCount -> do
        r <- readIORef runqueue
        writeChan f2a $ (Left $ ClockF2A_Count (length r))
      Left (ClockA2F_Deliver idx) -> do
        rq <- readIORef runqueue
        let callback = rq !! idx
        let rq' = deleteAtIndex idx rq
        writeIORef runqueue rq'
        writeChan callback ()
      Right msg -> do
        writeChan a2f' msg

  -- Define how to handle "eventually"
  let _eventually m = do
        -- Each eventually block creates a new channel
        callback <- newChan
        -- Add the write end to the runqueue
        rq <- readIORef runqueue
        let rq' = rq ++ [callback]
        writeIORef runqueue rq'
        -- Wait for the channel before executing the callback
        fork $ do
          () <- readChan callback
          m
        return ()

  -- [TODO]
{--                                 
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
--}


  let ?eventually = _eventually in
    f (p2f, f2p) (a2f', f2a') (undefined, undefined)
  return ()


{-
-- Example: fAuth
      fAuth is an asynchronous, one-shot, authenticated communication channel.
      The PIDs of the Sender and Receiver are encoded in the SID
      The sender can set the message (once). 
      After one (asynchronous) round, the receiver receives the message

-}

data FAuthF2P a = FAuthF2P_OK | FAuthF2P_Deliver a deriving (Eq, Read, Show)

fAuth :: MonadFunctionalityAsync m => Functionality msg (FAuthF2P msg) Void Void Void Void m
fAuth (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Parse SID as sender, recipient, ssid
  -- liftIO $ putStrLn $ "fauth sid: " ++ show ?sid
  let (pidS :: PID, pidR :: PID, ssid :: String) = readNote "fAuth" $ snd ?sid

  -- Store an optional message
  recorded <- newIORef False

  fork $ forever $ do
    (pid, m) <- readChan p2f
    liftIO $ putStrLn $ "[fAuth sid]: " ++ show ?sid
    liftIO $ putStrLn $ "[fAuth] message received: " ++ show (pidS, pidR, ssid)

    -- Sender can only send message once
    False <- readIORef recorded
    if not (pid == pidS) then fail "Invalid sender to fAuth" 
    else do
      writeIORef recorded True
      -- liftIO $ putStrLn $ "fAuth: notifying adv"
      -- ?leak m
      eventually $ writeChan f2p (pidR, FAuthF2P_Deliver m)
    writeChan f2p (pidS, FAuthF2P_OK)

  return ()

{-- Example environment using fAuth --}

testEnvAuthAsync z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestAuthAsync", show ("Alice", "Bob", ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    ?pass
  fork $ forever $ do
    m <- readChan a2z
    --liftIO $ putStrLn $ "Z: a sent " ++ show (m :: (SttCruptA2Z
    --                       (DuplexF2P Void (DuplexF2P Void (FAuthF2P String)))
    --                       (DuplexF2A ClockF2A (DuplexF2A (LeakF2A String) Void))))
    ?pass
  fork $ forever $ do
    Left f <- readChan f2z
    -- liftIO $ putStrLn $ "Z: f sent " ++ show f
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ("hi Bob"))

  -- Let the adversary deliver it
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  
  -- [TODO] Let the adversary see 
  -- () <- readChan pump 
  -- writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Right $ DuplexA2F_Left $ LeakA2F_Get

  -- [TODO] Let the environment force deliver
  -- () <- readChan pump 
  -- writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Right $ DuplexA2F_Left $ LeakA2F_Get

  () <- readChan pump 
  writeChan outp "environment output: 1"

testAuthAsync :: IO String
testAuthAsync = runITMinIO 120 $ execUC testEnvAuthAsync (idealProtocol) (runAsyncF fAuth) dummyAdversary


{-- Example environments using !fAuth --}

testEnvBangAsync z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestAuthAsync", "")
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
    ?pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " -- ++ show m
    ?pass
  fork $ forever $ do
    (ssid, Left f) <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " -- ++ show f
    ?pass

  -- Have Alice write a message
  () <- readChan pump
  --
  --let voidLeft sid = ("", show (voidSID, sid))
  --let sid' = voidLeft $ voidLeft $ ("ssidX", show ("Alice","Bob",""))
  let ssid1 = ("ssidX", show ("Alice","Bob",""))
  writeChan z2p ("Alice", (ssid1, "hi Bob"))

  -- Let the adversary read the buffer
  -- () <- readChan pump 
  -- writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Right $ DuplexA2F_Left $ LeakA2F_Get

  -- Let the adversary deliver it
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ (ssid1, Left (ClockA2F_Deliver 0))

  () <- readChan pump 
  writeChan outp "environment output: 1"


testBangAsync :: IO String
testBangAsync = runITMinIO 120 $ execUC testEnvBangAsync (idealProtocol) (bangF $ runAsyncF fAuth) dummyAdversary


-- TODO: A modular simulator
--runClockS s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
--  runDuplexS dummyAdversary s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f)

