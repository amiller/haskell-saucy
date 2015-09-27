 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses, FunctionalDependencies
  #-} 

-- Allow a functionality to leak messages to the adversary
-- However, control is returned to the leaker
module Leak where

import ProcessIO
import StaticCorruptions
import Duplex
import Safe

import Control.Concurrent.MonadIO
import Control.Monad (forever)
import Control.Monad.State (lift)
import Control.Monad.Reader

import Data.IORef.MonadIO
    
data LeakA2F   = LeakA2F_Get       deriving Show
data LeakF2A a = LeakF2A_Leaks [(SID, a)] deriving Show
data LeakPeerIn a = LeakPeerIn_Leak SID a deriving Show
data LeakPeerOut  = LeakPeerOut_OK    deriving Show

class HasFork m => MonadLeak a m | m -> a where
    leak :: a -> m ()

type LeakFuncT a = DuplexT (LeakPeerIn a) LeakPeerOut

{-
instance (HasFork m, MonadReader (Chan (LeakPeerIn a), Chan LeakPeerOut) m, MonadSID m) => MonadLeak a m where --(LeakFuncT a m) where
    leak a = do
      sid <- getSID
      liftIO $ putStrLn $ "leak:" ++ show sid
      (dW,dR) <- ask
      writeChan dW (LeakPeerIn_Leak sid a)
      LeakPeerOut_OK <- readChan dR
      liftIO $ putStrLn $ "leak: leak done"
      return ()
-}

instance (HasFork m, MonadReader (Chan (LeakPeerIn a), Chan LeakPeerOut) m, MonadSID m) => MonadLeak a m where --(LeakFuncT a m) where
    leak a = do
      sid <- getSID
      liftIO $ putStrLn $ "leak:" ++ show sid
      (dW,dR) <- ask
      writeChan dW (LeakPeerIn_Leak sid a)
      LeakPeerOut_OK <- readChan dR
      liftIO $ putStrLn $ "leak: leak done"
      return ()
{-
instance (HasFork m) => MonadLeak a (SIDMonadT (LeakFuncT a m)) where
    leak a = do
      sid <- getSID
      liftIO $ putStrLn $ "leak:" ++ show sid
      --(dW,dR) <- ask
      --writeChan dW (LeakPeerIn_Leak sid a)
      --LeakPeerOut_OK <- readChan dR
      lift $ duplexWrite (LeakPeerIn_Leak sid a)
      LeakPeerOut_OK <- lift duplexRead
      liftIO $ putStrLn $ "leak: leak done"
      return ()
-}
{-
instance (HasFork m) => MonadLeak a (LeakFuncT a (SIDMonadT m)) where
    leak a = do
      sid <- lift getSID
      liftIO $ putStrLn $ "leak:" ++ show sid
      --(dW,dR) <- ask
      --writeChan dW (LeakPeerIn_Leak sid a)
      --LeakPeerOut_OK <- readChan dR
      duplexWrite (LeakPeerIn_Leak sid a)
      LeakPeerOut_OK <- duplexRead
      liftIO $ putStrLn $ "leak: leak done"
      return ()
-}

fLeak crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  buffer <- newIORef []
  fork $ forever $ do
    LeakPeerIn_Leak sid a <- duplexRead
    liftIO $ putStrLn $ "[fLeak]: " ++ show sid
    modifyIORef buffer (++ [(sid,a)])
    duplexWrite LeakPeerOut_OK
  forever $ do
    LeakA2F_Get <- readChan a2f
    buf <- readIORef buffer
    writeChan f2a (LeakF2A_Leaks buf)

runLeakF
  :: (MonadSID m, HasFork m) =>
     (Crupt
      -> (Chan (PID, p2f), Chan (PID, f2p))
      -> (Chan a2f, Chan f2a)
      -> (Chan z2f, Chan f2z)
      -> DuplexT (LeakPeerIn leak) LeakPeerOut (SIDMonadT m) ())
     -> Crupt
     -> (Chan (PID, DuplexP2F Void p2f), Chan (PID, DuplexF2P Void f2p))
     -> (Chan (DuplexA2F LeakA2F a2f),   Chan (DuplexF2A (LeakF2A leak) f2a))
     -> (Chan (DuplexZ2F Void z2f),      Chan (DuplexF2Z Void f2z))
     -> m ()
runLeakF f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  runDuplexF fLeak f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z)

runLeakP :: (MonadSID m, HasFork m) =>
     (PID -> (Chan z2p, Chan p2z) -> (Chan f2p, Chan p2f) -> SIDMonadT m b)
     -> PID
     -> (Chan z2p, Chan p2z)
     -> (Chan (DuplexF2P Void f2p), Chan (DuplexP2F Void p2f))
     -> m b
runLeakP p pid (z2p, p2z) (f2p, p2f) = do
  -- `runLeakF f` does not change the "f2p" interface compared to `f`, 
  -- except for adding a layer of DuplexRight wrapping/unwrapping
  p2f' <- wrapWrite DuplexP2F_Right          p2f
  f2p' <- wrapRead (\(DuplexF2P_Right m)->m) f2p

  sid <- getSID
  let (_ :: String, rightConf :: String) = readNote ("runLeakP:" ++ show (snd sid)) $ snd sid
  let rightSID = extendSID sid "DuplexRight" rightConf

  runSID rightSID $ p pid (z2p, p2z) (f2p', p2f')

