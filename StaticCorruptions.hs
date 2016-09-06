 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies
  
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


deleteAtIndex index list = pref ++ (drop 1 suff) 
    where (pref,suff) = splitAt index list

type PID = String
type SID = (String, String)

type Crupt = Map PID ()

{----------------
 -- Session IDs
 --  tag:  a unique string, based on the callgraph of protocols/functionalities
 --  conf: a string containing configuration parameters
 ----------------}
class MonadReader SID m => MonadSID m where
    getSID :: m SID

instance MonadReader SID m => MonadSID m where
    getSID = ask

type SIDMonadT = ReaderT SID
runSID :: Monad m => SID -> SIDMonadT m a -> m a
runSID = flip runReaderT

--getSID :: MonadSID m => m SID
--getSID = ask

type Functionality p2f f2p a2f f2a z2f f2z m = Crupt -> (Chan p2f, Chan f2p) -> (Chan a2f, Chan f2a) -> (Chan z2f, Chan f2z) -> m ()

alterSIDF :: MonadSID m => (SID -> SID) -> Functionality p2f f2p a2f f2a z2f f2z (SIDMonadT m) -> Functionality p2f f2p a2f f2a z2f f2z m
alterSIDF trans f crupt p a z = do
  sid <- getSID
  runSID (trans sid) $ f crupt p a z

-- Extends SID A with SID B... 
-- A is included in the prefix of A|B, but the configuration of B (the second element) is preserved in A|B
extendSID :: SID -> String -> String -> SID
--extendSID sid (tag, conf) = (show (sid, tag), conf)
extendSID sid tag conf = (show (fst sid, tag), conf) -- This version drops the prior config

{- Provide input () until a value is received -}
runUntilOutput :: (MonadRand m) => Chan () -> (Chan () -> Chan a -> m ()) -> m a
runUntilOutput dump p = do
  pump <- newChan
  --dump <- newChan
  outp <- newChan
  --fork $ runDefault dump (p pump outp)
  fork $ p pump outp
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
     |  X  |
     A --- F

   -}
  z2p <- newChan; p2z <- newChan
  p2f <- newChan; f2p <- newChan
  f2a <- newChan; a2f <- newChan
  a2z <- newChan; z2a <- newChan
  a2p <- newChan; p2a <- newChan
  z2f <- newChan; f2z <- newChan

  z2exec <- newChan

  dump <- newChan
  
  fork $ do
    -- First, wait for the environment to choose an sid
    SttCrupt_SidCrupt sid crupt <- readChan z2exec

    fork $ runSID sid $ f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z)
    fork $ runSID sid $ partyWrapper p crupt (z2p, p2z) (f2p, p2f) (a2p, p2a) 
    -- reversing the order of dump and runSID breaks it??
    fork $ runDefault dump $ runSID sid $ a crupt (z2a, a2z) (p2a, a2p) (f2a, a2f)
    return ()

  runUntilOutput dump $ (\pump outp -> runDefault dump $ z z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp)

data SttCrupt_SidCrupt = SttCrupt_SidCrupt SID Crupt deriving Show

data SttCruptZ2A a b = SttCruptZ2A_A2P (PID, a) | SttCruptZ2A_A2F b deriving Show
data SttCruptA2Z a b = SttCruptA2Z_P2A (PID, a) | SttCruptA2Z_F2A b deriving Show


partyWrapper p crupt (z2p, p2z) (f2p, p2f) (a2p, p2a) = do
  -- Store a table that maps each PID to a channel (z2p,f2p,a2p) used
  -- to communicate with that instance of the protocol
  z2pid <- newIORef empty
  f2pid <- newIORef empty

  sid <- getSID
  
  -- subroutine to install a new party
  let newPid pid = do
        liftIO $ putStrLn $ "[" ++ show sid ++ "] Creating new party with pid:" ++ pid
        let newPid' _2pid p2_ tag = do
                     pp2_ <- newChan;
                     _2pp <- newChan;
                     fork $ forever $ do
                                  m <- readChan pp2_
                                  --liftIO $ putStrLn $ "party wrapper p->_ received " ++ tag
                                  writeChan p2_ (pid, m)
                     modifyIORef _2pid $ insert pid _2pp
                     return (_2pp, pp2_)
        z <- newPid' z2pid p2z "p2z"
        f <- newPid' f2pid p2f "p2f"
        fork $ p pid z f
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
    --liftIO $ putStrLn $ "party wrapper z->p received"
    getPid z2pid pid >>= flip writeChan m
    
  -- Route messages from functionality to honest parties (or to Adv)
  fork $ forever $ do
    (pid, m) <- readChan f2p
    if member pid crupt
    then do
      -- If corrupted, send to A instead of to P
      --liftIO $ putStrLn $ "party wrapper f->p received (corrupt)"
      writeChan p2a (pid, m)
    else do
      -- Otherwise pass messages through to P
      --liftIO $ putStrLn $ "party wrapper f->p received: " ++ show m
      getPid f2pid pid >>= flip writeChan m

  -- Pass messages to corrupt parties on to the functionatliy
  fork $ forever $ do
    (pid, m) <- readChan a2p
    if not $ member pid crupt then fail "tried to send corrupted!" else return undefined
    writeChan p2f (pid, m)

  return ()



{----------------------------
 Default / Ideal / Dummy  protocols and functionalities
 ----------------------------}

idealProtocol pid (z2p, p2z) (f2p, p2f) = do
  fork $ forever $ do
    m <- readChan z2p
    --liftIO $ putStrLn $ "idealProtocol received from z2p " ++ pid
    writeChan p2f m
  fork $ forever $ do
    m <- readChan f2p
    --liftIO $ putStrLn $ "idealProtocol received from f2p " ++ pid
    writeChan p2z m
  return ()

dummyAdversary crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >>= \mf -> 
      case mf of
        SttCruptZ2A_A2F b        -> writeChan a2f b
        SttCruptZ2A_A2P (pid, m) -> writeChan a2p (pid, m)
  fork $ forever $ readChan f2a >>= writeChan a2z . SttCruptA2Z_F2A
  fork $ forever $ readChan p2a >>= writeChan a2z . SttCruptA2Z_P2A
  return ()

voidAdversary crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >> pass
  fork $ forever $ readChan f2a >> pass
  fork $ forever $ readChan p2a >> pass
  return ()

dummyFunctionality crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  fork $ forever $ do
    (pid, m) <- readChan p2f
    --liftIO $ putStrLn $ "F: [" ++ pid ++ "] " ++ show m
    writeChan f2p (pid, m)
  fork $ forever $ do
    m :: String <- readChan a2f
    --liftIO $ putStrLn $ "F: A sent " ++ m
    writeChan f2a $ m
  return ()



testEnv z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do

  -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("sid1","") empty

  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    --writeChan outp ()
    pass

  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m
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
testExec = runRand $ execUC testEnv idealProtocol dummyFunctionality dummyAdversary




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


lemS dS a crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do

  a2pfS <- newChan
  a2fS <- wrapWrite SttCruptZ2A_A2F a2pfS
  a2pS <- wrapWrite SttCruptZ2A_A2P a2pfS

  pf2aS <- newChan
  p2aS <- newChan
  f2aS <- newChan

  fork $ forever $ do
    mf <- readChan pf2aS
    case mf of 
      SttCruptA2Z_F2A m -> writeChan f2aS m
      SttCruptA2Z_P2A m -> writeChan p2aS m
    
  fork $  a crupt (z2a, a2z) (p2aS, a2pS) (f2aS, a2fS)
  fork $ dS crupt (a2pfS, pf2aS) (p2a, a2p) (f2a, a2f)


{- Protocol Composition Theorem -}

-- Protocol Composition operation
--   This is different than the operation in UC Canetti, 
--   but the same as in Canetti Authentication

compose rho p pid (z2p, p2z) (f2p, p2f) = do
  r2p <- newChan
  p2r <- newChan
  fork $ rho pid (z2p, p2z) (r2p, p2r)
  fork $ p   pid            (p2r, r2p) (f2p, p2f)


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


compose_zBad rho z z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do

  z2pid <- newIORef empty
  f2pid <- newIORef empty

  z2aZ <- newChan
  a2zZ <- newChan
          
  z2pZ <- newChan
  p2zZ <- newChan

  z2execZ <- newChan

  -- Fork off local instance of z, and wait to receive sid and crupt.
  fork $ z z2execZ (p2zZ, z2pZ) (a2zZ, z2aZ) (f2z, z2f) outp
  SttCrupt_SidCrupt sid crupt <- readChan z2execZ
  writeChan z2exec $ SttCrupt_SidCrupt sid crupt

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

        fork $ rho pid (z2pp, pp2z) (f2pp, pp2f)
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




