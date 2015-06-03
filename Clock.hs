 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables
  
  #-} 


module Clock where

import StaticCorruptions
import ProcessIO

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map


data BarF_L2

-- Compose with Communicate
barF f g sid crupt (p2f, f2p) (a2f, f2a) = do

  f2pL <- wrap Left  f2p
  f2pR <- wrap Right f2p

  f2aL <- wrap Left  f2a
  f2aR <- wrap Right f2a

  a2fL <- newChan 
  a2fR <- newChan

  fork $ forever $ do
    mf <- readChan a2f
    case mf of Left  m -> writeChan m a2fL
               Right m -> writeChan m a2fR

  p2fL <- newChan
  p2fR <- newChan

  fork $ forever $ do
    mf <- readChan p2f
    case mf of Left  m -> writeChan m p2fL
               Right m -> writeChan m p2fR

  l2r <- newChan
  r2l <- newChan

  fork $ f (show $ (Left  sid :: Either SID SID)) crupt (p2fL, f2pL) (a2fL, f2aL) (r2l,l2r)
  fork $ g (show $ (Right sid :: Either SID SID)) crupt (p2fR, f2pR) (a2fR, f2aR) (l2r,r2l)

-- We can | compose with a functionality that doesn't expect it, like F | forget(G)
barForget f sid crupt (p2f, f2p) (a2f, f2a) (l2r,r2l) = f sid crupt (p2f, f2p) (a2f, f2a)



data SttCrupt_ClockF2A a = SttCrupt_ClockF2A_RoundOK PID | SttCrupt_ClockF2A_State Int (Map PID Bool) | SttCrupt_ClockF2A_F2A a deriving Show
data SttCrupt_ClockF2P a = SttCrupt_ClockF2P_Round Int | SttCrupt_ClockF2P_F2P a deriving Show
data SttCrupt_ClockA2F a = SttCrupt_ClockA2F_GetState  | SttCrupt_ClockA2F_A2F a deriving Show

data SttCrupt_ClockP2F a = SttCrupt_ClockP2F_GetRound  | SttCrupt_ClockP2F_RoundOK | SttCrupt_ClockP2F_P2F a deriving Show

data SttCrupt_ClockZ2P a = SttCrupt_ClockZ2P_GetRound  | SttCrupt_ClockZ2P_RoundOK | SttCrupt_ClockZ2P_Z2P a deriving Show
data SttCrupt_ClockP2Z a = SttCrupt_ClockP2Z_Round Int | SttCrupt_ClockP2Z_P2Z a deriving Show

{- Delay send (to party): actually puts in a bucket ready for other parties to receive. -}

class Monad m => MonadTimer m where
    getRound :: m Int

type ClockMonadT = ReaderT (Chan (), Chan Int)

instance MonadIO m => MonadTimer (ClockMonadT m) where
    getRound = do
      (getRoundQuery, getRoundResp) <- ask
      writeChan getRoundQuery ()
      readChan getRoundResp

instance MonadSID m => MonadSID (ClockMonadT m) where
    getSID = lift getSID

instance MonadTimer m => MonadTimer (SIDMonadT m) where
    getRound = lift getRound

-- Functionality wrapper
runClockF f crupt (p2f, f2p) (a2f, f2a) = do

  -- Store state for the clcok
  state <- newIORef empty
  round <- newIORef (0 :: Int)

  p2fF <- newChan
  f2pF <- wrap (\(pid,m) -> (pid,SttCrupt_ClockF2P_F2P m)) f2p
  a2fF <- newChan
  f2aF <- wrap SttCrupt_ClockF2A_F2A f2a

  -- Route messages from parties to clock, or to f
  fork $ forever $ do
    (pid, mf) <- readChan p2f
    case mf of SttCrupt_ClockP2F_RoundOK -> do
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
                 writeChan f2a $ SttCrupt_ClockF2A_RoundOK pid

               SttCrupt_ClockP2F_GetRound -> do
                 readIORef round >>= \r -> writeChan f2p $ (pid, SttCrupt_ClockF2P_Round r)

               SttCrupt_ClockP2F_P2F m -> do
                 writeChan p2fF (pid, m)

  -- Route messages from adversary to clock, or to f
  fork $ forever $ do
    mf <- readChan a2f
    case mf of SttCrupt_ClockA2F_GetState -> do
                 r <- readIORef round
                 s <- readIORef state
                 writeChan f2a $ SttCrupt_ClockF2A_State r s
               SttCrupt_ClockA2F_A2F m -> do
                 writeChan a2fF m
    
  getRoundQuery :: Chan () <- newChan
  getRoundResp <- newChan

  fork $ forever $ do readChan getRoundQuery >> readIORef round >>= writeChan getRoundResp

  fork $ flip runReaderT (getRoundQuery, getRoundResp) $ f crupt (p2fF, f2pF) (a2fF, f2aF)
  return ()

-- Protocol wrapper
runClockP p pid (z2p, p2z) (f2p, p2f) = do
  z2pP <- newChan
  p2zP <- wrap SttCrupt_ClockP2Z_P2Z p2z
  f2pP <- newChan
  p2fP <- wrap SttCrupt_ClockP2F_P2F p2f

  getRoundQuery <- wrap (const SttCrupt_ClockP2F_GetRound) p2f
  getRoundResp <- newChan

  fork $ forever $ do
    mf <- readChan z2p
    case mf of SttCrupt_ClockZ2P_GetRound -> do
                                          writeChan p2f SttCrupt_ClockP2F_GetRound
                                          SttCrupt_ClockF2P_Round r <- readChan f2p
                                          writeChan p2z $ SttCrupt_ClockP2Z_Round r
               SttCrupt_ClockZ2P_RoundOK  -> writeChan p2f SttCrupt_ClockP2F_RoundOK
               SttCrupt_ClockZ2P_Z2P m -> writeChan z2pP m

  fork $ forever $ do
    mf <- readChan f2p
    case mf of SttCrupt_ClockF2P_Round r -> writeChan getRoundResp r
               SttCrupt_ClockF2P_F2P m -> writeChan f2pP m

  fork $ flip runReaderT (getRoundQuery, getRoundResp) $ p pid (z2pP, p2zP) (f2pP, p2fP)
  return ()

-- Simulator wrapper
runClockS s crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  z2aS <- newChan
  a2zS <- newChan
  p2aS <- newChan
  a2pS <- newChan
  f2aS <- newChan
  a2fS <- newChan --wrap SttCrupt_ClockA2F_A2F a2f

  --getRoundQuery <- wrap (const SttCrupt_ClockA2F_GetState) a2f
  --getRoundResp <- newChan


  fork $ forever $ do
    mf <- readChan a2zS
    case mf of SttCruptA2Z_F2Z m -> writeChan a2z $ SttCruptA2Z_F2Z (SttCrupt_ClockF2A_F2A m)   --FIXME: SttCruptA2Z_F2Z should probably be renamed to SttCruptA2Z_F2A
               SttCruptA2Z_P2Z (pid,m) -> writeChan a2z $ SttCruptA2Z_P2Z (pid, SttCrupt_ClockF2P_F2P m)

  fork $ forever $ do
    (pid, SttCruptA2P_P2F m) <- readChan a2pS
    writeChan a2p (pid, SttCruptA2P_P2F (SttCrupt_ClockP2F_P2F m))

  fork $ forever $ do
    m <- readChan a2fS
    writeChan a2f (SttCrupt_ClockA2F_A2F m)

  fork $ forever $ do
    mf <- readChan f2a
    case mf of SttCrupt_ClockF2A_F2A m -> writeChan f2aS m
               --_ -> writeChan a2z $ SttCruptA2Z_F2Z mf
               SttCrupt_ClockF2A_RoundOK pid -> writeChan a2z (SttCruptA2Z_F2Z (SttCrupt_ClockF2A_RoundOK pid))
               SttCrupt_ClockF2A_State i m -> writeChan a2z (SttCruptA2Z_F2Z (SttCrupt_ClockF2A_State i m))

  fork $ forever $ do
    (pid :: PID, mf) <- readChan p2a
    case mf of SttCrupt_ClockF2P_Round r -> writeChan a2z (SttCruptA2Z_P2Z (pid, SttCrupt_ClockF2P_Round r))
               SttCrupt_ClockF2P_F2P m -> writeChan p2aS (pid, m)
    return ()

  fork $ forever $ do
    mf <- readChan z2a
    case mf of SttCruptZ2A_A2F (SttCrupt_ClockA2F_GetState) -> writeChan a2f SttCrupt_ClockA2F_GetState
               SttCruptZ2A_A2F (SttCrupt_ClockA2F_A2F m) -> writeChan z2aS (SttCruptZ2A_A2F m)
               SttCruptZ2A_A2P (pid, SttCrupt_ClockP2F_RoundOK) -> writeChan a2p $ (pid, SttCruptA2P_P2F SttCrupt_ClockP2F_RoundOK)
               SttCruptZ2A_A2P (pid, SttCrupt_ClockP2F_GetRound) -> writeChan a2p $ (pid, SttCruptA2P_P2F SttCrupt_ClockP2F_GetRound)
               SttCruptZ2A_A2P (pid, SttCrupt_ClockP2F_P2F m) -> writeChan z2aS (SttCruptZ2A_A2P (pid, m))

  --fork $ flip runReaderT (getRoundQuery, getRoundResp) $ s crupt (z2aS, a2zS) (p2aS, a2pS) (f2aS, a2fS)
  fork $ s crupt (z2aS, a2zS) (p2aS, a2pS) (f2aS, a2fS)
  return ()

{- Application example: Synchronous Authenticated Channels -}

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
                     writeChan f2p (pidR, msg)

  return ()


{- Do our theorems still hold under runClockP/runClockF? -}

testEnvBangBangSync (p2z, z2p) (a2z, z2a) pump outp = do
  -- Choose the sid and corruptions
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_SidCrupt ("sidTestBangBangSync","") empty
  _ <- readChan a2z
  pass

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
  writeChan z2p ("Alice", SttCrupt_ClockZ2P_RoundOK)
  () <- readChan pump
  writeChan z2p ("Bob", SttCrupt_ClockZ2P_RoundOK)

  -- Send a message
  () <- readChan pump
  writeChan z2p ("Alice", SttCrupt_ClockZ2P_Z2P (("ssidY",""), (("sssidX", show ("Alice", "Bob", 0::Int, "")), "hello!")))

  -- Advance the round counter
  () <- readChan pump
  writeChan z2p ("Alice", SttCrupt_ClockZ2P_RoundOK)
  () <- readChan pump
  writeChan z2p ("Bob", SttCrupt_ClockZ2P_RoundOK)

  -- Receive a message
  () <- readChan pump
  writeChan z2p ("Bob", SttCrupt_ClockZ2P_Z2P (("ssidY",""), (("sssidX", show ("Alice", "Bob", 0::Int, "")), undefined)))

  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F SttCrupt_ClockA2F_GetState

  () <- readChan pump 
  writeChan outp "environment output: 1"




testExecBangBangSyncReal :: IO String
testExecBangBangSyncReal = runRand $ execUC testEnvBangBangSync (runClockP squash) (runClockF $ bangF fSync) dummyAdversary

testExecBangBangSyncIdeal :: IO String
testExecBangBangSyncIdeal = runRand $ execUC testEnvBangBangSync (runClockP idealProtocol) (runClockF $ bangF $ bangF fSync) (runClockS squashS)
