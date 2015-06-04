 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies
  
  #-} 


module Duplex where

import StaticCorruptions
import ProcessIO

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map


data DuplexF2A a b = DuplexF2A_Left a | DuplexF2A_Right b deriving Show
data DuplexA2F a b = DuplexA2F_Left a | DuplexA2F_Right b deriving Show

data DuplexP2F a b = DuplexP2F_Left a | DuplexP2F_Right b deriving Show
data DuplexF2P a b = DuplexF2P_Left a | DuplexF2P_Right b deriving Show

data DuplexZ2P a b = DuplexZ2P_Left a | DuplexZ2P_Right b deriving Show
data DuplexP2Z a b = DuplexP2Z_Left a | DuplexP2Z_Right b deriving Show

data DuplexA2P a b = DuplexA2P_Left a | DuplexA2P_Right b deriving Show
data DuplexP2A a b = DuplexP2A_Left a | DuplexP2A_Right b deriving Show


-- Allow duplex communication
class Monad m => MonadDuplex a b m | m -> a b where
    duplexWrite :: a -> m ()
    duplexRead  ::      m b

--newtype DuplexT a b m x = DuplexT { _runDuplex :: ReaderT (Chan a, Chan b) m x }
data DuplexSentinel = DuplexSentinel
type DuplexT a b = ReaderT (Chan a, Chan b, DuplexSentinel)

instance HasFork m => MonadDuplex a b (DuplexT a b m) where
    duplexWrite a = ask >>= \(c, _, _) -> writeChan c a
    duplexRead    = ask >>= \(_, c, _) -> readChan c

instance MonadSID m => MonadSID (DuplexT a b m) where
    getSID = lift getSID

instance MonadDuplex a b m => MonadDuplex a b (SIDMonadT m) where
    duplexWrite = lift . duplexWrite
    duplexRead  = lift $ duplexRead

-- Functionality wrapper
runDuplexF fL fR crupt (p2f, f2p) (a2f, f2a) = do

  p2fL <- newChan
  p2fR <- newChan
  f2pL <- wrap (\(pid, m) -> (pid, DuplexF2P_Left  m)) f2p
  f2pR <- wrap (\(pid, m) -> (pid, DuplexF2P_Right m)) f2p

  a2fL <- newChan
  a2fR <- newChan
  f2aL <- wrap DuplexF2A_Left  f2a
  f2aR <- wrap DuplexF2A_Right f2a

  -- Route messages from parties to fL or fR
  fork $ forever $ do
    (pid, mf) <- readChan p2f
    case mf of DuplexP2F_Left  m -> writeChan p2fL (pid, m)
               DuplexP2F_Right m -> writeChan p2fR (pid, m)
    return ()

  -- Route messages from adversary to fL or fR
  fork $ forever $ do
    mf <- readChan a2f
    case mf of DuplexA2F_Left  m -> writeChan a2fL m
               DuplexA2F_Right m -> writeChan a2fR m

  l2r <- newChan
  r2l <- newChan

  fork $ flip runReaderT (l2r, r2l, DuplexSentinel) $ fL crupt (p2fL, f2pL) (a2fL, f2aL)
  fork $ flip runReaderT (r2l, l2r, DuplexSentinel) $ fR crupt (p2fR, f2pR) (a2fR, f2aR)
  return ()


runDuplexP pL pR pid (z2p, p2z) (f2p, p2f) = do

  z2pL <- newChan
  z2pR <- newChan
  p2zL <- wrap DuplexP2Z_Left  p2z
  p2zR <- wrap DuplexP2Z_Right p2z
  f2pL <- newChan
  f2pR <- newChan
  p2fL <- wrap DuplexP2F_Left  p2f
  p2fR <- wrap DuplexP2F_Right p2f

  fork $ forever $ do
    mf <- readChan z2p
    case mf of DuplexP2F_Left  m -> writeChan z2pL m
               DuplexP2F_Right m -> writeChan z2pR m

  fork $ forever $ do
    mf <- readChan f2p
    case mf of DuplexF2P_Left  m -> writeChan f2pL m
               DuplexF2P_Right m -> writeChan f2pR m

  l2r <- newChan
  r2l <- newChan

  fork $ flip runReaderT (l2r, r2l, DuplexSentinel) $ pL pid (z2pL, p2zL) (f2pL, p2fL)
  fork $ flip runReaderT (r2l, l2r, DuplexSentinel) $ pR pid (z2pR, p2zR) (f2pR, p2fR)
  return ()


-- Simulator wrapper
runDuplexS sL sR crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  z2aL <- newChan
  z2aR <- newChan
  a2zL <- newChan
  a2zR <- newChan
  p2aL <- newChan
  p2aR <- newChan
  a2pL <- wrap (\(pid, m) -> (pid, DuplexP2F_Left  m)) a2p
  a2pR <- wrap (\(pid, m) -> (pid, DuplexP2F_Right m)) a2p
  a2pR <- newChan
  f2aL <- newChan
  f2aR <- newChan
  a2fL <- wrap DuplexA2F_Left  a2f
  a2fR <- wrap DuplexA2F_Right a2f

  fork $ forever $ do
    mf <- readChan a2zL
    case mf of SttCruptA2Z_F2A       m  -> writeChan a2z $ SttCruptA2Z_F2A (     DuplexF2A_Left m)
               SttCruptA2Z_P2A (pid, m) -> writeChan a2z $ SttCruptA2Z_P2A (pid, DuplexF2P_Left m)

  fork $ forever $ do
    mf <- readChan a2zR
    case mf of SttCruptA2Z_F2A       m  -> writeChan a2z $ SttCruptA2Z_F2A (     DuplexF2A_Right m)
               SttCruptA2Z_P2A (pid, m) -> writeChan a2z $ SttCruptA2Z_P2A (pid, DuplexF2P_Right m)

  fork $ forever $ do
    mf <- readChan z2a
    case mf of SttCruptZ2A_A2P (pid, DuplexP2F_Left  m) -> writeChan z2aL $ SttCruptZ2A_A2P (pid, m)
               SttCruptZ2A_A2P (pid, DuplexP2F_Right m) -> writeChan z2aR $ SttCruptZ2A_A2P (pid, m)
               SttCruptZ2A_A2F (DuplexA2F_Left  m) -> writeChan z2aL $ SttCruptZ2A_A2F m
               SttCruptZ2A_A2F (DuplexA2F_Right m) -> writeChan z2aR $ SttCruptZ2A_A2F m

  fork $ forever $ do
    mf <- readChan f2a
    case mf of DuplexF2A_Left  m -> writeChan f2aL m
               DuplexF2A_Right m -> writeChan f2aR m

  fork $ forever $ do
    (pid, mf) <- readChan p2a
    case mf of DuplexF2P_Left  m -> writeChan p2aL (pid, m)
               DuplexF2P_Right m -> writeChan p2aR (pid, m)

  l2r <- newChan
  r2l <- newChan

  fork $ flip runReaderT (l2r, r2l, DuplexSentinel) $ sL crupt (z2aL, a2zL) (p2aL, a2pL) (f2aL, a2fL)
  fork $ flip runReaderT (r2l, l2r, DuplexSentinel) $ sR crupt (z2aR, a2zR) (p2aR, a2pR) (f2aR, a2fR)
  return ()


