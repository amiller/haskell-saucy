 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses
  #-} 

module ACast where

import ProcessIO
import StaticCorruptions
import Duplex
import Leak
import Async
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
data ACastF2A a = ACastF2A a deriving Show
data ACastA2F a = ACastA2F_Deliver PID deriving Show

assertNothing Nothing = return ()
assertNothing _ = fail "Not nothing"

fACast :: (MonadSID m, MonadLeak a m, MonadAsync m) =>
     Crupt
     -> (Chan (PID, ACastP2F a), Chan (PID, ACastF2P a))
     -> (Chan (ACastA2F a), Chan (ACastF2A a))
     -> (c, d)
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
    assert (pid == pidS) "Messages not from sender are ignored"
    readIORef value >>= assertNothing
    writeIORef value (Just m)        
    if Map.member pidS crupt then
        -- If sender is corrupt, no guarantees on liveness
        return ()
    else
        -- If sender is correct, every honest party outputs in 2 rounds
        forM_ parties $ \pid' -> do
           withinNRounds 2 $ do
             writeChan f2p (pid', ACastF2P_Deliver m)

  fork $ forever $ do
    ACastA2F_Deliver pid <- readChan a2f
    assert (elem pid parties) "Tried to deliver to unknown party"
    (Just m) <- readIORef value -- implicitly assert value has already been set
    writeChan f2p (pid, ACastF2P_Deliver m)

  return ()


{- Protocol ACast -}

data ACastMsg t = ACast_VAL t | ACast_ECHO (SignatureSig, t) | ACast_DECIDE ([Maybe SignatureSig], t)

splitDuplexF2P f2p = do
  left <- newChan
  right <- newChan
  fork $ forever $ do
    mf <- readChan f2p
    case mf of
      DuplexF2P_Left m -> writeChan left m 
      DuplexF2P_Right m -> writeChan right m
  return (left, right)

protACast :: (MonadSID m, HasFork m) =>
     PID
     -> (Chan (ACastP2F t), Chan (ACastF2P t))
     -> (Chan (DuplexF2P (SID, MulticastF2P (ACastMsg t)) (SignatureF2P t)),
         Chan (DuplexP2F (SID, t) (SignatureP2F t)))
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

  (f2p_mcast, f2p_sig) <- splitDuplexF2P f2p

  -- Receive messages from multicast
  fork $ forever $ do
    (sid', MulticastF2P_Deliver msg) <- readChan f2p_mcast
    let (pidS' :: PID, _ :: [PID], _ :: String) = read $ snd sid'
    case msg of
      ACast_VAL v -> do
          -- Check this is the *FIRST message from the right sender
          assert (pidS' == pidS) "[protACast]: VAL(v) from wrong sender"
          readIORef inputReceived >>= flip assert "[protACast]: Too many inputs received" . not
          writeIORef inputReceived True

          -- Create a signature
          sig <- undefined
          -- Multicast ECHO(sig, v)
          undefined

      ACast_ECHO (sig, v) -> 
          -- Check the signature using the fSignature instance for pidS'
          --  verifySig pidS' sig v
          -- Add this signature to a list
          undefined
      ACast_DECIDE (sigs, v) -> 
          -- Check each signature
          undefined
    

    
  return ()
