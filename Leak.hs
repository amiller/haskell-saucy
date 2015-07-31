 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses
  #-} 

-- Allow a functionality to leak messages to the adversary
-- However, control is returned to the leaker
module Leak where

import ProcessIO
import StaticCorruptions
import Duplex

import Control.Concurrent.MonadIO
import Control.Monad (forever)
import Control.Monad.State (lift)

import Data.IORef.MonadIO
    
data LeakA2F   = LeakA2F_Get       deriving Show
data LeakF2A a = LeakF2A_Leaks [(SID, a)] deriving Show
data LeakPeerIn a = LeakPeerIn_Leak SID a deriving Show
data LeakPeerOut  = LeakPeerOut_OK    deriving Show

class HasFork m => MonadLeak a m where
    leak :: a -> m ()

type LeakFuncT a = DuplexT (LeakPeerIn a) LeakPeerOut

instance MonadSID m => MonadSID (LeakFuncT a m) where
    getSID = lift getSID

instance (HasFork m, MonadSID m) => MonadLeak a (DuplexT (LeakPeerIn a) LeakPeerOut m) where
    leak a = do
      sid <- getSID
      duplexWrite (LeakPeerIn_Leak sid a)
      LeakPeerOut_OK <- duplexRead
      return ()

fLeak crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  buffer <- newIORef []
  fork $ forever $ do
    LeakPeerIn_Leak sid a <- duplexRead
    modifyIORef buffer ((sid,a):)
    duplexWrite LeakPeerOut_OK
  forever $ do
    LeakA2F_Get <- readChan a2f
    buf <- readIORef buffer
    writeChan f2a (LeakF2A_Leaks buf)

runLeakF f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  runDuplexF fLeak f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z)
