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


type MonadFunctionalityAsync m l = (MonadFunctionality m,
                                    ?eventually :: m () -> m (),
                                    ?leak :: l -> m ())

eventually :: MonadFunctionalityAsync m l => m () -> m ()
eventually m = ?eventually m

{-- The Asynchronous functionality wrapper --}
{--
   Lets other functionalities schedule events to be delivered in the future, in any order chosen by the adversary.
   Environment can "force" progress to move along, thus the adversary is thus unable to stall forever.
 --}
    
type CallbackID = Int
type Round = Int

{-- Types of messages exchanged with the clock --}
data ClockA2F = ClockA2F_GetCount | ClockA2F_Deliver Int | ClockA2F_GetLeaks deriving Show
data ClockF2A l = ClockF2A_Count Int | ClockF2A_Leaks [l] deriving Show
data ClockZ2F = ClockZ2F_MakeProgress deriving Show

{-- Implementation of MonadAsync --}

runAsyncF :: MonadFunctionality m =>
             (MonadFunctionalityAsync m l => Functionality p2f f2p a2f f2a Void Void m)
          -> Functionality p2f f2p (Either ClockA2F a2f) (Either (ClockF2A l) f2a) ClockZ2F Void m

runAsyncF f (p2f, f2p) (a2f, f2a) (z2f, f2z) = do

  -- Store state for the leakage buffer
  leaks <- newIORef []

  -- how to handle "leak"
  let _leak l = do
        buf <- readIORef leaks
        let buf' = buf ++ [l]
        writeIORef leaks buf'

  -- Store state for the clock
  runqueue <- newIORef []

  a2f' <- newChan
  f2a' <- wrapWrite Right f2a 
  z2f' <- newChan

  -- Adversary can query the current state, and deliver messages early
  fork $ forever $ do
    mf <- readChan a2f
    case mf of
      Left ClockA2F_GetCount -> do
        r <- readIORef runqueue
        writeChan f2a $ (Left $ ClockF2A_Count (length r))
      Left ClockA2F_GetLeaks -> do
        l <- readIORef leaks
        writeChan f2a $ (Left $ ClockF2A_Leaks l)
      Left (ClockA2F_Deliver idx) -> do
        rq <- readIORef runqueue
        let callback = rq !! idx
        let rq' = deleteAtIndex idx rq
        writeIORef runqueue rq'
        callback
      Right msg -> do
        writeChan a2f' msg

  --  how to handle "eventually"
  let _eventually m = do
        rq <- readIORef runqueue
        let rq' = rq ++ [m]
        writeIORef runqueue rq'


  -- TODO: add the "delay" option to the environment
  
  -- Allow the environment to force progress along
  fork $ forever $ do
    ClockZ2F_MakeProgress <- readChan z2f
    liftIO $ putStrLn $ "[fAsync] MakeProgress"
    rq <- readIORef runqueue
    if length rq > 0 then do
        -- Deliver the first message, remove it from buffer
        let callback = rq !! 0
        let rq' = deleteAtIndex 0 rq
        writeIORef runqueue rq'
        liftIO $ putStrLn $ "[fAsync] sending callback"
        callback
    else error "underflow"

  let ?eventually = _eventually; ?leak = _leak in
    f (p2f, f2p) (a2f', f2a') (z2f', f2z)
  return ()


{-
-- Example: fAuth
      fAuth is an asynchronous, one-shot, authenticated communication channel.
      The PIDs of the Sender and Receiver are encoded in the SID
      The sender can set the message (once). 
      After one (asynchronous) round, the receiver receives the message

-}

data FAuthF2P a = FAuthF2P_OK | FAuthF2P_Deliver a deriving (Eq, Read, Show)

fAuth :: MonadFunctionalityAsync m msg => Functionality msg (FAuthF2P msg) Void Void Void Void m
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
    _ <- readIORef recorded
    -- if _ == False then error "recorded problem" else do
    if not (pid == pidS) then error "Invalid sender to fAuth" 
    else do
      writeIORef recorded True
      ?leak m
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
    liftIO $ putStrLn $ "Z: a sent " ++ show m
    ?pass
  fork $ forever $ do
    f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show f
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", ("hi Bob"))

  -- Let the adversary see 
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks

  -- Let the adversary deliver it
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)
  

  -- [TODO] Let the environment force deliver
  -- () <- readChan pump 
  -- writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Right $ DuplexA2F_Left $ LeakA2F_Get

  () <- readChan pump 
  writeChan outp "environment output: 1"

testAuthAsync :: IO String
testAuthAsync = runITMinIO 120 $ execUC testEnvAuthAsync (idealProtocol) (runAsyncF fAuth) dummyAdversary


{----------------------------------}
{- runAsyncF !F vs !(runAsyncF F) -}
{----------------------------------}
{-
   While it's possible to compose async and bang directly with
   bangF (runAsyncF F), this isn't generally what we want.
   In particular, the JUC theorem (see Multisession.hs) does not
   hold in general.
 -}

_bangFAsync :: MonadFunctionality m => Chan (SID, l) -> Chan (Chan (), Chan ()) -> (forall m. MonadFunctionalityAsync m l => Functionality p2f f2p a2f f2a Void Void m) ->  Functionality p2f f2p a2f f2a Void Void m
_bangFAsync _leak _eventually f = f
  where
    ?leak = \l -> writeChan _leak (?sid, l)
    ?eventually = \m -> do
      cb <- newChan
      ok <- newChan
      writeChan _eventually (cb, ok)
      fork $ do
        () <- readChan cb
        m
      readChan ok


bangFAsync
  :: MonadFunctionalityAsync m (SID, l) =>
     (forall m'. MonadFunctionalityAsync m' l => Functionality p2f f2p a2f f2a Void Void m') ->
     Functionality (SID, p2f) (SID, f2p) (SID, a2f) (SID, f2a) Void Void m
bangFAsync f (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  _leak <- newChan
  _eventually <- newChan

  fork $ forever $ do
    (cb,ok) <- readChan _eventually
    eventually $ do
      writeChan cb ()
    writeChan ok ()

  fork $ forever $ do
    l <- readChan _leak
    ?leak l

  bangF (_bangFAsync _leak _eventually f) (p2f, f2p) (a2f, f2a) (z2f, f2z)



{-- Example environments using !fAuth --}

--testEnvAsyncBang :: 
testEnvAsyncBang z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestAuthAsync", "")
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
    ?pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m
    ?pass

  -- Have Alice write a message
  () <- readChan pump
  let ssid1 = ("ssidX", show ("Alice","Bob",""))
  writeChan z2p ("Alice", (ssid1, "hi Bob"))

  -- Let the adversary read the buffer
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks

  -- Let the adversary deliver it
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

  () <- readChan pump 
  writeChan outp "environment output: 1"


testAsyncBang :: IO String
testAsyncBang = runITMinIO 120 $ execUC testEnvAsyncBang (idealProtocol) (runAsyncF $ bangFAsync fAuth) dummyAdversary



{-- Counter example of why !Async(F) does not work, even though Async(!F) is OK --}
{--
testEnvBangAsync z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestAuthAsync", "")
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
    ?pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m
    ?pass
  fork $ forever $ do
    (ssid, f) <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " -- ++ show f
    ?pass

  -- Have Alice write a message
  () <- readChan pump
  let ssid1 = ("ssidX", show ("Alice","Bob",""))
  writeChan z2p ("Alice", (ssid1, "hi Bob"))

  -- Let the adversary read the buffer
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ (ssid1, Left ClockA2F_GetLeaks)

  -- Let the adversary deliver it
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ (ssid1, Left (ClockA2F_Deliver 0))

  () <- readChan pump 
  writeChan outp "environment output: 1"


testBangAsync :: IO String
testBangAsync = runITMinIO 120 $ execUC testEnvBangAsync (idealProtocol) (bangF $ runAsyncF fAuth) dummyAdversary
--}
