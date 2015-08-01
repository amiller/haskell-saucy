 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances  
  #-} 


module CoinsAsync where

import ProcessIO
import StaticCorruptions
import Duplex
import Leak    -- provides "leak" instruction
import Async   -- provides "registerCallback", "byNextRound"

import Control.Concurrent.MonadIO
import Control.Monad (forever)
import Control.Monad.State
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map

getNbits 0 = return 0
getNbits n | n < 0 = fail "negative bits?"
getNbits n = do
  b <- getBit
  rest <- getNbits (n-1)
  return $ 2*rest + if b then 0 else 1

get32bytes :: (Num a, MonadRand m) => m a
get32bytes = getNbits (32*8)
    
fUnspentCoin crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Parse SID as owner, ssid
  sid <- getSID
  let (pidOwner :: PID, ssid :: String) = read $ snd sid

  fork $ do
    (pid, mf) <- readChan p2f
    if not (pid == pidOwner) then fail "only owner can spend coin" else return ()

    -- If the owner is honest, then the new transaction has a random ID
--    newtx <- getRandomString

data LedgerP2F = LedgerP2F_Transfer Int PID
data LedgerF2A = LedgerF2A_Transfer PID Int PID
data LedgerF2P = LedgerF2P_Transfer PID Int


fLedger crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Initial allocation is encoded
  sid <- getSID
  let (initialLedger :: Map PID Int, ssid :: String) = read $ snd sid

  ledger <- newIORef initialLedger

  -- 
  fork $ forever $ do
    (pidS, LedgerP2F_Transfer val pidR) <- readChan p2f
    curLedger <- readIORef ledger

    -- Check valid values
    assert (val > 0) $ "must be positive amount"
    let balanceS = Map.findWithDefault 0 pidS curLedger
    let balanceR = Map.findWithDefault 0 pidR curLedger
    assert (balanceS >= val) $ "can't transfer more than current balance"

    -- Update ledger immediately
    let newLedger  = Map.insert pidS (balanceS - val) curLedger
    let newLedger' = Map.insert pidS (balanceR + val) curLedger
    writeIORef ledger newLedger'

    -- Leak to adversary
    leak $ LedgerF2A_Transfer pidS val pidR

    -- Tell recipient within 2 rounds
    byNextRound $ do
      byNextRound $ do
        writeChan f2p $ (pidR, LedgerF2P_Transfer pidS val)

    return ()

