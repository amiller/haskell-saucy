{-# LANGUAGE ScopedTypeVariables, ImplicitParams, Rank2Types
  #-} 


module Both where

import StaticCorruptions
import ProcessIO
import Safe

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map


data BothF2A a b = BothF2A_Left a | BothF2A_Right b deriving Show
data BothA2F a b = BothA2F_Left a | BothA2F_Right b deriving Show

data BothF2Z a b = BothF2Z_Left a | BothF2Z_Right b deriving Show
data BothZ2F a b = BothZ2F_Left a | BothZ2F_Right b deriving Show

data BothP2F a b = BothP2F_Left a | BothP2F_Right b deriving Show
data BothF2P a b = BothF2P_Left a | BothF2P_Right b deriving Show

data BothZ2P a b = BothZ2P_Left a | BothZ2P_Right b deriving Show
data BothP2Z a b = BothP2Z_Left a | BothP2Z_Right b deriving Show

data BothA2P a b = BothA2P_Left a | BothA2P_Right b deriving Show
data BothP2A a b = BothP2A_Left a | BothP2A_Right b deriving Show


-- Functionality wrapper

runBothF
  :: ((?sid::SID), HasFork m) =>
      ((?sid::SID) => Crupt
       -> (Chan (PID, p2fL), Chan (PID, f2pL))
       -> (Chan a2fL, Chan f2aL)
       -> (Chan z2fL, Chan f2zL)
       -> m ())
   -> ((?sid::SID) => Crupt
       -> (Chan (PID, p2fR), Chan (PID, f2pR))
       -> (Chan a2fR, Chan f2aR)
       -> (Chan z2fR, Chan f2zR)
       -> m ())
     -> Crupt
     -> (Chan (PID, BothP2F p2fL p2fR), Chan (PID, BothF2P f2pL f2pR))
     -> (Chan (BothA2F a2fL a2fR), Chan (BothF2A f2aL f2aR))
     -> (Chan (BothZ2F z2fL z2fR), Chan (BothF2Z f2zL f2zR))
     -> m ()
runBothF fL fR crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do

  p2fL <- newChan
  p2fR <- newChan
  f2pL <- wrapWrite (\(pid, m) -> (pid, BothF2P_Left  m)) f2p
  f2pR <- wrapWrite (\(pid, m) -> (pid, BothF2P_Right m)) f2p

  a2fL <- newChan
  a2fR <- newChan
  f2aL <- wrapWrite BothF2A_Left  f2a
  f2aR <- wrapWrite BothF2A_Right f2a

  z2fL <- newChan
  z2fR <- newChan
  f2zL <- wrapWrite BothF2Z_Left  f2z
  f2zR <- wrapWrite BothF2Z_Right f2z

  -- Route messages from parties to fL or fR
  fork $ forever $ do
    (pid, mf) <- readChan p2f
    case mf of BothP2F_Left  m -> writeChan p2fL (pid, m)
               BothP2F_Right m -> writeChan p2fR (pid, m)
    return ()

  -- Route messages from adversary to fL or fR
  fork $ forever $ do
    mf <- readChan a2f
    case mf of BothA2F_Left  m -> writeChan a2fL m
               BothA2F_Right m -> writeChan a2fR m

  -- Route messages from environment to fL or fR
  fork $ forever $ do
    mf <- readChan z2f
    case mf of BothZ2F_Left  m -> writeChan z2fL m
               BothZ2F_Right m -> writeChan z2fR m

  sid <- getSID
  let (leftConf :: String, rightConf :: String) = readNote ("runBothF:" ++ show (snd sid)) $ snd sid
  let  leftSID = extendSID sid "BothLeft"   leftConf
  let rightSID = extendSID sid "BothRight" rightConf

  fork $ runSID  leftSID $ fL crupt (p2fL, f2pL) (a2fL, f2aL) (z2fL, f2zL)
  fork $ runSID rightSID $ fR crupt (p2fR, f2pR) (a2fR, f2aR) (z2fR, f2zR)
  return ()


{-- Both *protocols* 
 --}

runBothP
  :: ((?sid::SID), HasFork m) =>
      ((?sid::SID) => PID
       -> (Chan z2pL, Chan p2zL)
       -> (Chan f2pL, Chan p2fL)
       -> m ())
   -> ((?sid::SID) => PID
       -> (Chan z2pR, Chan p2zR)
       -> (Chan f2pR, Chan p2fR)
       -> m ())
     -> PID
     -> (Chan (BothZ2P z2pL z2pR), Chan (BothP2Z p2zL p2zR))
     -> (Chan (BothF2P f2pL f2pR), Chan (BothP2F p2fL p2fR))
     -> m ()
runBothP pL pR pid (z2p, p2z) (f2p, p2f) = do

  z2pL <- newChan
  z2pR <- newChan
  p2zL <- wrapWrite BothP2Z_Left  p2z
  p2zR <- wrapWrite BothP2Z_Right p2z
  f2pL <- newChan
  f2pR <- newChan
  p2fL <- wrapWrite BothP2F_Left  p2f
  p2fR <- wrapWrite BothP2F_Right p2f

  fork $ forever $ do
    mf <- readChan z2p
    case mf of BothZ2P_Left  m -> writeChan z2pL m
               BothZ2P_Right m -> writeChan z2pR m

  fork $ forever $ do
    mf <- readChan f2p
    case mf of BothF2P_Left  m -> writeChan f2pL m
               BothF2P_Right m -> writeChan f2pR m

  sid <- getSID
  let (leftConf :: String, rightConf :: String) = readNote ("runBothF:" ++ show (snd sid)) $ snd sid
  let  leftSID = extendSID sid "BothLeft"   leftConf
  let rightSID = extendSID sid "BothRight" rightConf

  fork $ runSID  leftSID $ pL pid (z2pL, p2zL) (f2pL, p2fL)
  fork $ runSID rightSID $ pR pid (z2pR, p2zR) (f2pR, p2fR)
  return ()


