 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses
  #-} 

module Multicast where

import ProcessIO
import StaticCorruptions
import Duplex
import Leak
import Async
import Multisession
import Safe

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.State
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map

{- fMulticast: a multicast functionality -}

forMseq_ xs f = sequence_ $ map f xs

data MulticastF2P a = MulticastF2P_OK | MulticastF2P_Deliver a deriving Show
data MulticastF2A a = MulticastF2A a deriving Show
data MulticastA2F a = MulticastA2F_Deliver PID a deriving Show

--instance (MonadSID m) => MonadLeak String (LeakFuncT (SID, String) m) where
--    leak x = lift getSID >>= \sid -> lift $ leak (sid, x)

fMulticast :: (MonadSID m, MonadLeak t m, MonadAsync m) =>
     Crupt
     -> (Chan (PID, t), Chan (PID, MulticastF2P t))
     -> (Chan (MulticastA2F t), Chan (MulticastF2A t))
     -> (Chan Void, Chan Void)
     -> m ()
fMulticast crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender and set of parties is encoded in SID
  sid <- getSID
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticast" $ snd sid

  if not $ member pidS crupt then
      -- Only activated by the designated sender
      fork $ forever $ do
        (pid, m) <- readChan p2f
        if pid == pidS then do
          leak m
          forMseq_ parties $ \pidR -> do
             byNextRound $ writeChan f2p (pidR, MulticastF2P_Deliver m)
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
protMulticast :: (MonadSID m, HasFork m) =>
     PID
     -> (Chan t, Chan (MulticastF2P t))
     -> (Chan (SID, FAuthF2P t),
         Chan (SID, t))
     -> m ()
protMulticast pid (z2p, p2z) (f2p, p2f) = do
  -- Sender and set of parties is encoded in SID
  sid <- getSID
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
        assert (pidS' == pidS) "wrong sender"
        assert (pidR' == pid)  "wrong recipient"
        writeChan p2z (MulticastF2P_Deliver m)
      FAuthF2P_OK -> writeChan cOK ()

  return ()



{-- The dummy simmulator for protMulticast --}

simMulticast crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  {-
  What happens when the environment asks the adversary to query the buffer?
  -} 
  sid <- getSID
  let ("", s1) = readNote "sim multicast s1" $ snd sid
  let ("", s2) = readNote "sim multicast s2" $ s1
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "sim multicast" $ s2

  fork $ forever $ do
    mf <- readChan z2a
    case mf of
      -- TODO: For corrupted parties, the simulator translates "FAuthP2F_Msg m" messages intended for !fAuth (real world) into "MulticastA2F deliver" messages
      -- This requires tedious programming to get right, I wish we could just search for it!
      SttCruptZ2A_A2P (pid, m) -> undefined

      SttCruptZ2A_A2F (DuplexA2F_Left (ClockA2F_Deliver r idx)) -> do
        -- The protocol guarantees that clock events are inserted in correct order, 
        -- so delivery can be passed through directly
        writeChan a2f (DuplexA2F_Left (ClockA2F_Deliver r idx))
      SttCruptZ2A_A2F (DuplexA2F_Right (DuplexA2F_Left LeakA2F_Get)) -> do
        -- If the "ideal" leak buffer contains "Multicast m",
        -- then the "real" leak buffer should contain [(pid, (sid, m)] for every party
        writeChan a2f (DuplexA2F_Right (DuplexA2F_Left LeakA2F_Get))
        DuplexF2A_Right (DuplexF2A_Left (LeakF2A_Leaks buf)) <- readChan f2a
        let extendRight conf = show ("", conf)
        let resp = case buf of
              []       ->  []
              [(_, m)] ->  [(extendSID (extendSID (extendSID sid "DuplexRight" undefined) "DuplexRight" undefined) "" (show (pidS, pid, "")), 
                             m)
                            | pid <- parties]
        writeChan a2z $ SttCruptA2Z_F2A $ DuplexF2A_Right $ DuplexF2A_Left $ LeakF2A_Leaks resp
        
  return ()

testEnvMulticast
  :: (MonadDefault m) =>
     Chan SttCrupt_SidCrupt
     -> (Chan (PID, MulticastF2P String), Chan (PID, String))
     -> (Chan (SttCruptA2Z
               (DuplexF2P Void (DuplexF2P Void (SID, FAuthF2P String)))
               (DuplexF2A ClockF2A (DuplexF2A (LeakF2A String) (SID, Void)))),
         Chan (SttCruptZ2A 
               (DuplexP2F Void (DuplexP2F Void (SID, String)))
               (DuplexA2F ClockA2F (DuplexA2F LeakA2F (SID, Void)))))
     -> (Chan (DuplexF2Z ClockF2Z (DuplexF2Z Void Void)), 
         Chan (DuplexZ2F ClockZ2F (DuplexZ2F Void Void)))
     -> Chan ()
     -> Chan [Char]
     -> m ()
testEnvMulticast z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  let sid = ("sidTestMulticast", extendRight $ extendRight $ show ("Alice", ["Alice", "Bob"], ""))
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
  writeChan z2p ("Alice", "I'm Alice")

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
testMulticastReal = runRand $ execUC testEnvMulticast (runAsyncP $ runLeakP protMulticast) (runAsyncF $ runLeakF $ bangF fAuth) dummyAdversary

testMulticastIdeal :: IO String
testMulticastIdeal = runRand $ execUC testEnvMulticast (runAsyncP $ runLeakP idealProtocol) (runAsyncF $ runLeakF fMulticast) simMulticast
