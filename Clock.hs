 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables
  
  #-} 


module Clock where

import ProcessIO
import StaticCorruptions
import Duplex

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map

data ClockP2F = ClockP2F_RoundOK | ClockP2F_GetRound deriving Show
data ClockF2P = ClockF2P_Round Int deriving Show
data ClockA2F = ClockA2F_GetState deriving Show
data ClockF2A = ClockF2A_RoundOK PID | ClockF2A_State Int (Map PID Bool) deriving Show
data ClockPeerIn  = ClockPeerIn_GetRound deriving Show
data ClockPeerOut = ClockPeerOut_Round Int deriving Show


fClock crupt (p2f, f2p) (a2f, f2a) = do

  -- Store state for the clock
  state <- newIORef empty
  round <- newIORef (0 :: Int)

  -- Route messages from parties to clock
  fork $ forever $ do
    (pid, mf) <- readChan p2f
    case mf of ClockP2F_RoundOK -> do
                 if member pid crupt then fail "adversary shouldn't call roundOK" else return ()
                 s <- readIORef state
                 if not $ member pid s then modifyIORef state (insert pid False)
                 else do
                   modifyIORef state (insert pid True)
                   -- Check if all the bits in the map are True. 
                   -- If so, then increment round and reset the bits
                   s <- readIORef state
                   if Map.foldr (&&) True s then do
                     modifyIORef state (Map.map (const False))
                     modifyIORef round (+ 1)
                     r <- readIORef round
                     liftIO $ putStrLn $ "All 'roundOK' received. New round: " ++ show r
                   else return ()
                 writeChan f2a $ ClockF2A_RoundOK pid

               ClockP2F_GetRound -> readIORef round >>= writeChan f2p . (,) pid . ClockF2P_Round

  -- Route messages from adversary to clock
  fork $ forever $ do
    ClockA2F_GetState <- readChan a2f
    r <- readIORef round
    s <- readIORef state
    writeChan f2a $ ClockF2A_State r s

  fork $ forever $ do
    ClockPeerIn_GetRound <- duplexRead
    r <- readIORef round
    duplexWrite $ ClockPeerOut_Round r

  return ()


class Monad m => MonadTimer m where
    getRound :: m Int

instance MonadDuplex ClockPeerIn ClockPeerOut m => MonadTimer m where
    getRound = do
      duplexWrite ClockPeerIn_GetRound
      ClockPeerOut_Round r <- duplexRead
      return r



runClockF f crupt (p2f, f2p) (a2f, f2a) = do
  runDuplexF fClock f crupt (p2f, f2p) (a2f, f2a)

runClockP p crupt (p2f, f2p) (a2f, f2a) = do
  runDuplexP idealProtocol p crupt (p2f, f2p) (a2f, f2a)

runClockS s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  runDuplexS dummyAdversary s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f)




fSync crupt (p2f, f2p) (a2f, f2a) = do
  -- Parse SID as sender, recipient, ssid
  sid <- getSID
  --liftIO $ putStrLn $ "fSync: about to read sid: " -- ++ show sid
  --liftIO $ putStrLn $ show $ fst sid
  --liftIO $ putStrLn $ show $ snd sid

  let (pidS :: PID, pidR :: PID, round :: Int, ssid :: String) = read $ snd sid

  -- Store an optional message
  message <- newIORef Nothing

  fork $ forever $ do
    (pid, m :: String) <- readChan p2f
    r <- getRound

    -- Sender must send his message before or during $round
    case () of _ | r <= round && pid == pidS -> do
                     writeIORef message (Just m)
                     --liftIO $ putStrLn $ "fSync: notifying adv"
                     writeChan f2a (pid, m)

    -- Recipient can request his message in any r > $round
                 | r >  round && pid == pidR -> do
                     msg <- readIORef message
                     writeChan f2p (pid, msg)

  return ()


testEnvSquashBangSync z2exec (p2z, z2p) (a2z, z2a) pump outp = do
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

  -- Register both parties
  () <- readChan pump
  writeChan z2p ("Alice", DuplexP2F_Left ClockP2F_RoundOK)
  () <- readChan pump
  writeChan z2p ("Bob",   DuplexP2F_Left ClockP2F_RoundOK)

  -- Send a message
  () <- readChan pump
  writeChan z2p ("Alice", DuplexP2F_Right (("ssidY",""), (("sssidX", show ("Alice", "Bob", 0::Int, "")), "hello!")))

  -- Advance the round counter
  () <- readChan pump
  writeChan z2p ("Alice", DuplexP2F_Left ClockP2F_RoundOK)
  () <- readChan pump
  writeChan z2p ("Bob",   DuplexP2F_Left ClockP2F_RoundOK)

  -- Receive a message
  () <- readChan pump
  writeChan z2p ("Bob", DuplexP2F_Right (("ssidY",""), (("sssidX", show ("Alice", "Bob", 0::Int, "")), undefined)))
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ DuplexA2F_Left ClockA2F_GetState

  () <- readChan pump 
  writeChan outp "environment output: 1"


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

-- Identities:
--  runClockP idealProtocol  ~= idealProtocol
--  runClockS dummyAdvesrary ~= dummyAdversary


testSquashBangIdeal :: IO String
testSquashBangIdeal = runRand $ execUC testEnvSquashBangSync idealProtocol (runClockF $ bangF $ bangF $ fSync) (runClockS squashS)

testSquashBangReal :: IO String
testSquashBangReal = runRand $ execUC testEnvSquashBangSync (runClockP squash) (runClockF $ bangF $ fSync) dummyAdversary

