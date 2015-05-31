 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables
  
  #-} 

{- 

 -}

module StaticCorruptions where

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)
import Control.Monad.Reader

import System.Random

import ProcessIO

import Data.IORef.MonadIO
import Data.Map.Strict

type PID = String
type SID = String

{- Provide input () until a value is received -}
runUntilOutput :: (MonadRand m) => (Chan () -> Chan a -> ReaderT (Chan ()) m ()) -> m a
runUntilOutput p = do
  pump <- newChan
  dump <- newChan
  outp <- newChan
  fork $ runDefault dump (p pump outp)
  c <- multiplex dump outp
  let _run = do
        writeChan pump ()
        o <- readChan c
        case o of 
          Left  () -> _run
          Right a  -> return a in _run

test3 :: (MonadDefault m, MonadRand m) => Chan () -> Chan Int -> m ()
test3 pump outp = test3' 0 where
    test3' n = do
      () <- readChan pump
      b1 <- getBit
      b2 <- getBit
      b3 <- getBit
      b4 <- getBit;
      --lift $ putStrLn $ show [b1,b2,b3,b4];
      if (b1 == b2 && b2 == b3 && b3 == b4 && b4 == True) then
          writeChan outp n
      else
          pass;
          test3' (n+1)

--test3run :: IO [Int]
--test3run = replicateM 10 $ runRand $ runUntilOutput test3


{- UC Experiments -}
execUC z p f a = do
  {- 
    UC communication layout

     Z --- party[Pi]
     |  /  |
     A --- F

   -}
  z2p <- newChan; p2z <- newChan
  p2f <- newChan; f2p <- newChan
  f2a <- newChan; a2f <- newChan
  a2z <- newChan; z2a <- newChan
  a2p <- newChan; p2a <- newChan

  fork $ do
    -- First, wait for the environment to choose an sid
    SttCruptZ2A_SidCrupt sid crupt <- readChan z2a

    fork $ f sid crupt (p2f, f2p) (a2f, f2a)
    fork $ p sid crupt (z2p, p2z) (f2p, p2f) (a2p, p2a) 
    fork $ a sid crupt (z2a, a2z) (p2a, a2p) (f2a, a2f)

    writeChan a2z SttCruptA2Z_Ok

  runUntilOutput $ z (p2z, z2p) (a2z, z2a)


data SttCruptZ2A a b = SttCruptZ2A_SidCrupt SID (Map PID ()) | SttCruptZ2A_A2P (PID, a) | SttCruptZ2A_A2F b deriving Show

data SttCruptP2A a b = SttCruptP2A_Z2P (PID, a) | SttCruptP2A_F2P (PID, b) | SttCruptP2A_Ok deriving Show

data SttCruptA2P a = SttCruptA2P_P2F a deriving Show
data SttCruptA2Z a b = SttCruptA2Z_P2Z a | SttCruptA2Z_F2Z b | SttCruptA2Z_Ok deriving Show

--data SttCruptP2Z = SttCruptP2Z (PID, String)     | SttCruptP2Z_Crupt (Map PID ())
--data SttCruptP2F = SttCruptP2F (PID, String)     | SttCruptP2F_Crupt (Map PID ())

--data SttCruptZ2P = SttCruptZ2P (PID, String)     | SttCruptZ2P_Crupt
--data SttCruptF2P = SttCruptF2P (PID, String)     | SttCruptF2P_Crupt

wrap f c = do
  d <- newChan 
  fork $ forever $ readChan d >>= writeChan c . f 
  return d

-- Adversary must deliver: Either [String] (String,*)
partyWrapper p sid crupt (z2p, p2z) (f2p, p2f) (a2p, p2a) = do
  -- Store a table that maps each PID to a channel (z2p,f2p,a2p) used
  -- to communicate with that instance of the protocol
  z2pid <- newIORef empty
  f2pid <- newIORef empty

  -- subroutine to install a new party
  let newPid pid = do
        liftIO $ putStrLn $ "[" ++ sid ++ "] Creating new party with pid:" ++ pid
        let newPid' _2pid p2_ tag = do
                     pp2_ <- newChan;
                     _2pp <- newChan;
                     fork $ forever $ do
                                  m <- readChan pp2_
                                  liftIO $ putStrLn $ "party wrapper p->_ received " ++ tag
                                  writeChan p2_ (pid, m)
                     modifyIORef _2pid $ insert pid _2pp
                     return (_2pp, pp2_)
        z <- newPid' z2pid p2z "p2z"
        f <- newPid' f2pid p2f "p2f"
        fork $ p pid sid z f
        return ()

  -- Retrieve the {z2p,f2p,a2p} channel by PID (or install a new party if this is 
  -- the first such message)
  let getPid _2pid pid = do
        b <- return . member pid =<< readIORef _2pid
        if not b then newPid pid else return ()
        readIORef _2pid >>= return . (! pid)

  -- Route messages from environment to honest parties
  fork $ forever $ do
    (pid, m) <- readChan z2p
    if member pid crupt then fail "env sent to corrupted party!" else return undefined
    liftIO $ putStrLn $ "party wrapper z->p received"
    getPid z2pid pid >>= flip writeChan m
    
  -- Route messages from functionality to honest parties (or to Adv)
  fork $ forever $ do
    (pid, m) <- readChan f2p
    if member pid crupt
    then do
      -- If corrupted, send to A instead of to P
      liftIO $ putStrLn $ "party wrapper f->p received (corrupt)"
      writeChan p2a $ SttCruptP2A_F2P (pid, m)
    else do
      -- Otherwise pass messages through to P
      liftIO $ putStrLn $ "party wrapper f->p received"
      getPid f2pid pid >>= flip writeChan m

  fork $ forever $ do
    (pid, SttCruptA2P_P2F m) <- readChan a2p
    if not $ member pid crupt then fail "tried to send corrupted!" else return undefined
    writeChan p2f (pid, m)

  return ()



{----------------------------
 Default / Ideal / Dummy  protocols and functionalities
 ----------------------------}

idealProtocol pid sid (z2p, p2z) (f2p, p2f) = do
  fork $ forever $ do
    m <- readChan z2p
    liftIO $ putStrLn $ "idealProtocol received from z2p " ++ pid
    writeChan p2f m
  fork $ forever $ do
    m <- readChan f2p
    liftIO $ putStrLn $ "idealProtocol received from f2p " ++ pid
    writeChan p2z m
  return ()

dummyAdversary sid crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >>= \mf -> 
      case mf of
        SttCruptZ2A_A2F b        -> writeChan a2f b
        SttCruptZ2A_A2P (pid, m) -> writeChan a2p (pid, m)
  fork $ forever $ readChan f2a >>= writeChan a2z . SttCruptA2Z_F2Z
  fork $ forever $ readChan p2a >>= writeChan a2z . SttCruptA2Z_P2Z
  return ()

dummyFunctionality sid crupt (p2f, f2p) (a2f, f2a) = do
  fork $ forever $ do
    (pid, m) <- readChan p2f
    liftIO $ putStrLn $ "F: [" ++ pid ++ "] " ++ show m
    writeChan f2p (pid, m)
  fork $ forever $ do
    m <- readChan a2f
    liftIO $ putStrLn $ "F: A sent " ++ show m
    writeChan f2a $ m
  return ()
              
testEnv (p2z, z2p) (a2z, z2a) pump outp = do
  -- Choose the sid and corruptions
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_SidCrupt "sid1" empty
  _ <- readChan a2z
  pass

  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    --writeChan outp ()
    pass

  fork $ forever $ do
    m <- readChan a2z
    --liftIO $ putStrLn $ "Z: a sent " ++ show m
    writeChan outp "environment output: 1"

  () <- readChan pump
  liftIO $ putStrLn "pump"
  b <- getBit
  if b then
      writeChan z2p ("Alice", show "0")
  else
      writeChan z2p ("Bob", show "1")

  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F "ok"

testExec :: IO String
testExec = runRand $ execUC testEnv (partyWrapper idealProtocol) dummyFunctionality dummyAdversary


{- Dummy lemma -}
--
-- Suppose  (p,f) ~dummy~ (q,g)... i.e.,
-- There exists a simulator dS for the dummy adversary dA such that
--    forall z. execUC z p f dA ~ execUC z q g dS
--
-- Then there exists a transformer lemS such that:
--    forall a z. execUC z p f a ~ execUC z q g (lemS dS a)

-- Intuition: lemS runs a and dS locally
--      z <--|--> a <--> dS <--|--> f or p


lemS dS a sid crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do

  a2pfS <- newChan
  a2fS <- wrap SttCruptZ2A_A2F a2pfS
  a2pS <- wrap SttCruptZ2A_A2P a2pfS

  pf2aS <- newChan
  p2aS <- newChan
  f2aS <- newChan

  fork $ forever $ do
    mf <- readChan pf2aS
    case mf of 
      SttCruptA2Z_F2Z m -> writeChan f2aS m
      SttCruptA2Z_P2Z m -> writeChan p2aS m
    
  fork $  a sid crupt (z2a, a2z) (p2aS, a2pS) (f2aS, a2fS)
  fork $ dS sid crupt (a2pfS, pf2aS) (p2a, a2p) (f2a, a2f)


{- Protocol Composition Theorem -}

-- Protocol Composition operation
--   This is different than the operation in UC Canetti, 
--   but the same as in Canetti Authentication

compose rho p pid sid (z2p, p2z) (f2p, p2f) = do
  r2p <- newChan
  p2r <- newChan
  fork $ rho pid sid (z2p, p2z) (r2p, p2r)
  fork $ p   pid sid            (p2r, r2p) (f2p, p2f)


-- Theorem statement:
--       (pi,f) ~ (phi,g) --> (rho^pi,f) ~ (rho^phi,g)

-- Proof:
--   Suppose (pi,f) emulates (phi,g). Then there exists a simulator s for the dummy
--   adversary such that
--     forall z. execUC z pi f dA ~ execUC z phi g s
--
--   Suppose for contradiction rho^pi ~!~ rho^phi.
--   Then there exists a bad environment z, such that
--     forall s. execUC z rho^pi f dA ~!~ execUC z rho^phi g s
--
--   From this z we can construct a distingushing environment zBad such that
--     execUC (zBad z) pi f dA ~!~ execUC (zBad z) phi g s
--
--   This contradicts the initial assumption.
--
--   Intuition:
--      zBad runs an instance of z locally, and threads it through rho.
--          - | z <--> rho <--|--> p

--      This gives a perfect simulation of  
--           execUC z rho^pi f dA
--      on the left side and of
--           execUC z rho^phi g s
--      on the right.


compose_zBad rho z (p2z, z2p) (a2z, z2a) pump outp = do

  z2pid <- newIORef empty
  f2pid <- newIORef empty

  z2aZ <- newChan
  a2zZ <- newChan
          
  z2pZ <- newChan
  p2zZ <- newChan

  -- Fork off local instance of z, and wait to receive sid and crupt.
  fork $ z (p2zZ, z2pZ) (a2zZ, z2aZ) pump outp
  SttCruptZ2A_SidCrupt sid crupt <- readChan z2aZ
  writeChan z2a $ SttCruptZ2A_SidCrupt sid crupt

  -- After intercepting the (sid,crupt), a and z communicate faithfully
  fork $ forever $ readChan a2z >>= writeChan a2zZ
  fork $ forever $ readChan z2aZ >>= writeChan z2a

  -- subroutine to install a new instance of rho
  let newPid pid = do
        -- When rho communicates to z, it is routed correctly
        pp2z <- newChan
        z2pp <- newChan
        fork $ forever $ readChan pp2z >>= writeChan p2zZ . ((,) pid)
        modifyIORef z2pid $ insert pid z2pp
                       
        -- When rho communicates to F, it is routed to P
        pp2f <- newChan
        f2pp <- newChan
        fork $ forever $ readChan pp2f >>= writeChan z2p . ((,) pid)
        modifyIORef f2pid $ insert pid f2pp

        fork $ rho pid sid (z2pp, pp2z) (f2pp, pp2f)
        return ()

  let getPid _2pid pid = do
        b <- return . member pid =<< readIORef _2pid
        if not b then newPid pid else return ()
        readIORef _2pid >>= return . (! pid)

  -- Routing between p and rho
  fork $ forever $ do
    (pid, m) <- readChan p2z
    if member pid crupt then fail "p sent from corrupted party!" else return undefined
    getPid f2pid pid >>= flip writeChan m

  -- Routing between z and rho
  fork $ forever $ do
    (pid, m) <- readChan z2pZ
    if member pid crupt then fail "env (z) sent to corrupted party!" else return undefined
    getPid z2pid pid >>= flip writeChan m

