 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses
  #-} 

module ACast where

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
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

{- fACast: an asynchronous broadcast functionality -}
{-
   Narrative description:
   - Each party inputs a message (of type `a`, a parameter)
   - This functionality inlines an assumption on the fault tolerance
     TODO: Express `assume n>3t` as a generic functionality operator
   - If `a`
 -}

data ACastP2F a = ACastP2F_Input a deriving Show
data ACastF2P a = ACastF2P_OK | ACastF2P_Deliver a deriving Show
data ACastF2A a = ACastF2A a deriving Show
data ACastA2F a = ACastA2F_Deliver PID deriving Show

assertNothing Nothing = return ()
assertNothing _ = fail "Not nothing"

fACast :: (MonadSID m, MonadLeak a m, MonadAsync m) =>
     Crupt
     -> (Chan (PID, ACastP2F a), Chan (PID, ACastF2P a))
     -> (Chan (ACastA2F a), Chan (ACastF2A a))
     -> (c, d)
     -> m ()
fACast crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sender, set of parties, and tolerance parameter is encoded in SID
  sid <- getSID
  let (pidS :: PID, parties :: [PID], t :: Int, sssid :: String) = read $ snd sid

  -- Check the fault tolerance parameters
  let n = length parties
  assert (Map.size crupt <= t) "Fault tolerance assumption violated"
  assert (n > 3*t) "Invalid fault tolerance parameter (must be 3t<n)"

  -- Store the first sent value
  value <- newIORef (Nothing :: Maybe a)

  -- Allow sender to choose the input
  fork $ forever $ do
    (pid, ACastP2F_Input m) <- readChan p2f
    assert (pid == pidS) "Messages not from sender are ignored"
    readIORef value >>= assertNothing
    writeIORef value (Just m)        
    if Map.member pidS crupt then
        -- If sender is corrupt, no guarantees on liveness
        return ()
    else
        -- If sender is correct, every honest party outputs in 2 rounds
        forM_ parties $ \pid' -> do
           withinNRounds 2 $ do
             writeChan f2p (pid', ACastF2P_Deliver m)

  fork $ forever $ do
    ACastA2F_Deliver pid <- readChan a2f
    assert (elem pid parties) "Tried to deliver to unknown party"
    (Just m) <- readIORef value -- implicitly assert value has already been set
    writeChan f2p (pid, ACastF2P_Deliver m)

  return ()


{- Protocol ACast -}
