 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables
  
  #-} 

{- 

 -}

import Control.Concurrent.MonadIO
import Data.IORef.MonadIO
import Control.Monad (forever)
import ProcessIO
import StaticCorruptions

-- Commitment is impossible to realize in the standard model

data P2Fcom = Commit Bool | Open | Receive

fCom sid crupt (p2f, f2p) (a2f, f2a) = do
  -- Parse sid as defining two players
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid

  s2f <- newChan
  r2f <- newChan
  fork $ forever $ do
    (pid, m) <- readChan p2f
    case () of _ | pid == pidS -> writeChan s2f m
                 | pid == pidR -> writeChan r2f m

  opened <- newIORef False

  -- Receive a value from the sender
  Commit b <- readChan s2f

  -- Notify the adversary
  writeChan f2a ()

  -- Wait for the sender to "open"
  fork $ do
    Open <- readChan s2f
    writeIORef opened True

  -- Let the receiver poll, revealing the value only after "open"
  forever $ do
    Receive <- readChan r2f
    o <- readIORef opened
    writeChan f2p (pidR, if o then Just b else Nothing)


{- Commitment is impossible in the plain model
   Theorem 6 from 
     Universally Composable Commitments
     https://eprint.iacr.org/2001/055 

   Suppose F_com is realizable.
   Then there is a protocol p, and a simulator s (parameterized by adversary a), such that
     forall a z. execUC z wrap(p) a dF ~ execUC z wrap(dP) (s a) fCom 

   We will show this is impossible, by constructing a distinguisher z and adversary a, such that
     let (z, a) = zbad p s
     execUC z wrap(p) a dummyF ~/~ execUC z wrap(idealP) (s a) fCom

 -}
