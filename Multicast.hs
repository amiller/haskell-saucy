{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-} 

module Multicast where

import ProcessIO
import StaticCorruptions
import Multisession
import Async

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map

{- fMulticast: a multicast functionality -}

forMseq_ xs f = sequence_ $ map f xs

data MulticastF2P a = MulticastF2P_OK | MulticastF2P_Deliver a deriving Show
data MulticastF2A a = MulticastF2A a deriving Show
data MulticastA2F a = MulticastA2F_Deliver PID a deriving Show

fMulticast :: MonadFunctionalityAsync m t =>
  Functionality t (MulticastF2P t) (MulticastA2F t) (MulticastF2A t) Void Void m
fMulticast (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender and set of parties is encoded in SID
  let sid = ?sid :: SID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticast" $ snd sid

  if not $ member pidS ?crupt then
      -- Only activated by the designated sender
      fork $ forever $ do
        (pid, m) <- readChan p2f
        if pid == pidS then do
          ?leak m
          forMseq_ parties $ \pidR -> do
             eventually $ writeChan f2p (pidR, MulticastF2P_Deliver m)
          writeChan f2p (pidS, MulticastF2P_OK)
        else fail "multicast activated not by sender"
  else do
      -- If sender is corrupted, arbitrary messages can be delivered (once) to parties in any order
      delivered <- newIORef (empty :: Map PID ())
      fork $ forever $ do
         MulticastA2F_Deliver pidR m <- readChan a2f
         del <- readIORef delivered
         if member pidR del then return () 
         else do
           writeIORef delivered (insert pidR () del)
           writeChan f2p (pidR, MulticastF2P_Deliver m)
  return ()


{-- An !fAuth hybrid protocol realizing fMulticast --}
protMulticast :: MonadProtocol m =>
     Protocol t (MulticastF2P t) (SID, FAuthF2P t) (SID, t) m
protMulticast (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  let sid = ?sid :: SID
  let pid = ?pid :: PID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "protMulticast:" $ snd sid

  cOK <- newChan

  -- Only activated by the designated sender
  fork $ forever $ do
    m <- readChan z2p
    if pid == pidS then do
        liftIO $ putStrLn $ "protMulticast: PARTIES " ++ show parties
        forMseq_ parties $ \pidR -> do
          -- Send m to each party, through a separate functionality
          let ssid' = ("", show (pid, pidR, ""))
          writeChan p2f (ssid', m)
          readChan cOK
        writeChan p2z MulticastF2P_OK

    else fail "multicast activated not by sender"

  -- Messages send from other parties are relayed here
  fork $ forever $ do
    (ssid, mf) <- readChan f2p
    case mf of 
      FAuthF2P_Deliver m -> do
        -- Double check this is the intended message
        let (pidS' :: PID, pidR' :: PID, _ :: String) = readNote "protMulticast_2" $ snd ssid
        require (pidS' == pidS) "wrong sender"
        require (pidR' == pid)  "wrong recipient"
        writeChan p2z (MulticastF2P_Deliver m)
      FAuthF2P_OK -> writeChan cOK ()

  return ()


{-- The dummy simmulator for protMulticast --}
simMulticast (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  {-
  What happens when the environment asks the adversary to query the buffer?
  -}
  let sid = ?sid :: SID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "sim multicast" (snd sid)

  fork $ forever $ do
    mf <- readChan z2a
    case mf of
      -- TODO: For corrupted parties, the simulator translates "FAuthP2F_Msg m" messages intended for !fAuth (real world) into "MulticastA2F deliver" messages
      -- This requires tedious programming to get right, I wish we could just search for it!
      SttCruptZ2A_A2P (pid, m) -> undefined

      SttCruptZ2A_A2F (Left (ClockA2F_Deliver idx)) -> do
        -- The protocol guarantees that clock events are inserted in correct order, 
        -- so delivery can be passed through directly
        writeChan a2f (Left (ClockA2F_Deliver idx))
      SttCruptZ2A_A2F (Left ClockA2F_GetLeaks) -> do
        -- If the "ideal" leak buffer contains "Multicast m",
        -- then the "real" leak buffer should contain [(pid, (sid, m)] for every party
        writeChan a2f (Left ClockA2F_GetLeaks)
        (Left (ClockF2A_Leaks buf)) <- readChan f2a
        let extendRight conf = show ("", conf)
        let resp = case buf of
              []       ->  []
              [m] ->  [(extendSID sid "" (show (pidS, pid, "")),
                         m)
                      | pid <- parties]
        writeChan a2z $ SttCruptA2Z_F2A $ Left (ClockF2A_Leaks resp)
        
  return ()


testEnvMulticast
  :: MonadEnvironment m =>
     Environment (MulticastF2P String) String (SttCruptA2Z (SID, FAuthF2P String) (Either (ClockF2A (SID, String)) (SID, Void))) (SttCruptZ2A (SID, String) (Either ClockA2F (SID, Void))) Void ClockZ2F String m
testEnvMulticast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestMulticast", show ("Alice", ["Alice", "Bob"], ""))
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
    f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show f
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p ("Alice", "I'm Alice")

  -- Let the adversary see
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks

  -- Optional: Adversary delivers messages out of order
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 1)

  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ Left (ClockA2F_Deliver 0)

  -- Advance to round 1
  -- () <- readChan pump
  -- writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)
  -- () <- readChan pump
  -- writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  -- Advance to round 2
  -- () <- readChan pump
  -- writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)
  -- () <- readChan pump
  -- writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  () <- readChan pump 
  writeChan outp "environment output: 1"

testMulticastReal :: IO String
testMulticastReal = runITMinIO 120 $ execUC testEnvMulticast (protMulticast) (runAsyncF $ bangFAsync $ fAuth) dummyAdversary

testMulticastIdeal :: IO String
testMulticastIdeal = runITMinIO 120 $ execUC testEnvMulticast (idealProtocol) (runAsyncF fMulticast) simMulticast

