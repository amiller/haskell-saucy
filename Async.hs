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
eventually = ?eventually

leak :: MonadFunctionalityAsync m l => l -> m ()
leak = ?leak

{-- The Asynchronous functionality wrapper --}
{--
   Lets other functionalities schedule events to be delivered in the future, in any order chosen by the adversary.
   Environment can "force" progress to move along, thus the adversary is thus unable to stall forever.
 --}
    
type CallbackID = Int
type Round = Int

{-- Types of messages exchanged with the clock --}
data ClockA2F = ClockA2F_GetCount | ClockA2F_Deliver Int | ClockA2F_GetLeaks deriving Show
data ClockF2A l = ClockF2A_Pass | ClockF2A_Count Int | ClockF2A_Leaks [l] deriving Show
data ClockZ2F = ClockZ2F_MakeProgress deriving Show
data ClockP2F a = ClockP2F_Pass | ClockP2F_Through a deriving Show



{-- Implementation of MonadAsync --}

deleteNth i xs = l ++ r where (l,(_:r)) = splitAt i xs

runAsyncF :: MonadFunctionality m =>
             (MonadFunctionalityAsync m l => Functionality p2f f2p a2f f2a Void Void m)
          -> Functionality (ClockP2F p2f) f2p (Either ClockA2F a2f) (Either (ClockF2A l) f2a) ClockZ2F Void m
runAsyncF f (p2f, f2p) (a2f, f2a) (z2f, f2z) = do

  -- Store state for the leakage buffer
  leaks <- newIORef []

  -- how to handle "leak"
  let _leak l = do
        modifyIORef leaks (++ [(l)])
        return ()

  -- Store state for the clock
  runqueue <- newIORef []

  a2f' <- newChan
  f2a' <- wrapWrite Right f2a 
  z2f' <- newChan

  -- Allow protocols to pass
  p2f' <- newChan
  fork $ forever $ do
    mf <- readChan p2f
    case mf of
        (_, ClockP2F_Pass) -> writeChan f2a $ Left ClockF2A_Pass
        (pid, ClockP2F_Through m) -> writeChan p2f' (pid, m)

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
                     q <- readIORef runqueue
                     modifyIORef runqueue (deleteNth idx)
                     writeChan (q !! idx) ()
      Right msg -> writeChan a2f' msg

  --  how to handle "eventually"
  let _eventually m = do
        c :: Chan () <- newChan
        modifyIORef runqueue (++ [c])
        fork $ readChan c >> m
        return ()

  -- TODO: add the "delay" option to the environment
  
  -- Allow the environment to force progress along
  fork $ forever $ do
    ClockZ2F_MakeProgress <- readChan z2f
    liftIO $ putStrLn $ "[fAsync] MakeProgress"
    rq <- readIORef runqueue
    if length rq > 0 then do
        -- Deliver the first message, remove it from buffer
        modifyIORef runqueue (deleteNth 0)
        liftIO $ putStrLn $ "[fAsync] sending callback"        
        writeChan (rq !! 0) ()
    else error "underflow"

  let ?eventually = _eventually; ?leak = _leak in
    f (p2f', f2p) (a2f', f2a') (z2f', f2z)
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
      leak m
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
  writeChan z2p ("Alice", ClockP2F_Through ("hi Bob"))

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
   There are two approaches to compose async and bang. Regardless of which we choose,
   we have to handle updating the session ID, since "leak" doesn't normally include it.

   (Option 1):    bangF (runAsyncF F)
         this isn't generally what we want, since we think there being a single
         queue of scheduled tasks and a single queue of leaks
   (Option 2):    runAsyncF (bangF)
         However, the generalized version of theories like JUC don't automatically follow,
         so the following is new and must be proven.
           async(F) --p-> async(!F)
           async(F) --q-> async(G)
           --------------------------------
           async(F) --!q.p-> async(!G)
 -}

_bangFAsyncInstance :: MonadFunctionality m => Chan (SID, l) -> Chan (Chan (), Chan ()) -> (forall m. MonadFunctionalityAsync m l => Functionality p2f f2p a2f f2a Void Void m) ->  Functionality p2f f2p a2f f2a Void Void m
_bangFAsyncInstance _leak _eventually f = f
  where
    ?leak = \l -> writeChan _leak (?sid, l)
    ?eventually = \m -> do
      cb :: Chan () <- newChan
      ok :: Chan () <- newChan
      writeChan _eventually (cb, ok)
      fork $ readChan cb >> m
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
    ?eventually $ do
      writeChan cb ()
    writeChan ok ()

  fork $ forever $ do
    l <- readChan _leak
    leak l

  bangF (_bangFAsyncInstance _leak _eventually f) (p2f, f2p) (a2f, f2a) (z2f, f2z)



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
  writeChan z2p ("Alice", ClockP2F_Through (ssid1, "hi Bob"))

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



type MonadAsyncP m = (MonadProtocol m,
                           ?pass :: m ())
runAsyncP :: MonadProtocol m =>
  (MonadAsyncP m => Protocol z2p p2z f2p p2f m) ->
     Protocol z2p p2z f2p (ClockP2F p2f) m
runAsyncP prot (z2p, p2z) (f2p, p2f) = do
  let pass = do
        writeChan p2f ClockP2F_Pass
  p2f' <- wrapWrite ClockP2F_Through p2f
  let ?pass = pass in
     prot (z2p, p2z) (f2p,p2f')
        
