 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses
  
  #-} 

module AsyncBroadcast where

import ProcessIO
import StaticCorruptions
import Duplex
import Leak
import Async

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.State
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map

{- Messages exchanged with broadcast -}

data MulticastP2Z a = MulticastP2Z_OK | MulticastP2Z_Deliver a deriving Show
data MulticastF2A a = MulticastF2A a deriving Show

fMulticast :: (MonadSID m, MonadLeak (MulticastF2A t) m, MonadAsync m) =>
     Crupt
     -> (Chan (PID, t), Chan (PID, MulticastP2Z t))
     -> (Chan a, Chan (MulticastF2A t))
     -> (c, d)
     -> m ()
fMulticast crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender and set of parties is encoded in SID
  sid <- getSID
  let (pidS :: PID, parties :: [PID], sssid :: String) = read $ snd sid

  -- Only activated by the designated sender
  fork $ forever $ do
    (pid, m) <- readChan p2f
    if pid == pidS then do
        leak (MulticastF2A m)
        forM parties $ \pidR -> do
           byNextRound $ writeChan f2p (pidR, MulticastP2Z_Deliver m)
    else fail "multicast activated not by sender"
  return ()

{-runLeakMulticast :: (MonadSID m, MonadAsync m) =>
                   Crupt
                   -> (Chan (PID, DuplexP2F Void p2f),
                       Chan (PID, DuplexF2P Void (MulticastP2Z p2f)))
                   -> (Chan (DuplexA2F LeakA2F a2f),
                       Chan (DuplexF2A (LeakF2A (MulticastF2A p2f)) (MulticastF2A p2f)))
                   -> (Chan (DuplexZ2F Void z2f), Chan (DuplexF2Z Void f2z))
                   -> m ()-}
--runLeakMulticast = runLeakF fMulticast

{-- An !fAuth hybrid protocol --}
protMulticast :: (MonadSID m, HasFork m) =>
     PID
     -> (Chan t, Chan (MulticastP2Z t))
     -> (Chan (SID, FAuthF2P t),
         Chan (SID, t))
     -> m ()
protMulticast pid (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  sid <- getSID
  let (pidS :: PID, parties :: [PID], sssid :: String) = read $ snd sid

  cOK <- newChan

  -- Only activated by the designated sender
  fork $ forever $ do
    m <- readChan z2p
    if pid == pidS then do
        forM parties $ \pidR -> do
          -- Send m to each party, through a separate functionality
          let ssid' = ("", show (pid, pidR, ""))
          writeChan p2f (ssid', m)
          readChan cOK
        writeChan p2z MulticastP2Z_OK

    else fail "multicast activated not by sender"

  -- Messages send from other parties are relayed here
  fork $ forever $ do
    (ssid, mf) <- readChan f2p
    case mf of 
      FAuthF2P_Deliver m -> do
        -- Double check this is the intended message
        let (pidS' :: PID, pidR' :: PID, _ :: String) = read $ snd ssid
        assert (pidS' == pidS) "wrong sender"
        assert (pidR' == pid)  "wrong recipient"
        writeChan p2z (MulticastP2Z_Deliver m)
      FAuthF2P_OK -> writeChan cOK ()

  return ()




testEnvMulticast
  :: (MonadDefault m, Show a) =>
     Chan SttCrupt_SidCrupt
     -> (Chan (PID, a), Chan (PID, (SID, [Char])))
     -> (Chan (SttCruptA2Z
                           (DuplexF2P Void (DuplexF2P Void (SID, FAuthF2P (SID, [Char]))))
                           (DuplexF2A
                              ClockF2A (DuplexF2A (LeakF2A (PID, (SID, [Char]))) (SID, Void)))),
         Chan (SttCruptZ2A a4 (DuplexA2F ClockA2F (DuplexA2F LeakA2F b))))
     -> (Chan (DuplexF2Z ClockF2Z (DuplexF2Z Void Void)), 
         Chan (DuplexZ2F ClockZ2F (DuplexZ2F Void Void)))
     -> Chan ()
     -> Chan [Char]
     -> m ()
testEnvMulticast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestMulticast", show ("Alice", ["Alice", "Bob"], ""))
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
  writeChan z2p ("Alice", (("ssidX",show ("Alice",["Alice","Bob"],"")), "I'm Alice"))

  -- Let the adversary see
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Right $ DuplexA2F_Left $ LeakA2F_Get

  -- Optional: Adversary delivers messages out of order
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Left $ ClockA2F_Deliver 1 1

  -- Advance to round 1
  () <- readChan pump
  writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)
  () <- readChan pump
  writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  -- Advance to round 2
  () <- readChan pump
  writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)
  () <- readChan pump
  writeChan z2f (DuplexZ2F_Left ClockZ2F_MakeProgress)

  () <- readChan pump 
  writeChan outp "environment output: 1"

testMulticastReal :: IO String
testMulticastReal = runRand $ execUC testEnvMulticast (runAsyncP (runLeakP protMulticast)) (runAsyncF $ runLeakF $ bangF fAuth) dummyAdversary

testMulticastIdeal :: IO String
testMulticastIdeal = runRand $ execUC undefined (runAsyncP $ runLeakP idealProtocol) (runAsyncF (runLeakF fMulticast)) undefined
