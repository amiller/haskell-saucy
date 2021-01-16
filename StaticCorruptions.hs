{-# LANGUAGE Rank2Types, ImplicitParams, ConstraintKinds,
             ScopedTypeVariables
  #-} 

{- 

 -}


module StaticCorruptions where

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_, replicateM)
import System.Random

import ProcessIO

import Data.IORef.MonadIO
import Data.Map.Strict hiding (drop,splitAt)

deleteAtIndex index list = pref ++ (drop 1 suff) 
    where (pref,suff) = splitAt index list


{----------------
 -- Session IDs
 --  tag:  a unique string, based on the callgraph of protocols/functionalities
 --  conf: a string containing configuration parameters
 ----------------}

type SID = (String, String)

-- Extends SID A with SID B... 
-- A is included in the prefix of A|B, but the configuration of B (the second element) is not preserved in A|B
extendSID :: SID -> String -> String -> SID
--extendSID sid (tag, conf) = (show (sid, tag), conf)
extendSID sid tag conf = (show (fst sid, tag), conf) -- This version drops the prior config

-- Player IDs
type PID = String

-- Corruption maps
type Crupt = Map PID ()

{-- Functionality class --}
type MonadFunctionality m =
  (MonadITM m,
    ?sid :: SID,
    ?crupt :: Crupt)
  
type Functionality p2f f2p a2f f2a z2f f2z m = MonadFunctionality m => (Chan (PID, p2f), Chan (PID, f2p)) -> (Chan a2f, Chan f2a) -> (Chan z2f, Chan f2z) -> m ()


runFunctionality :: MonadITM m => SID -> Crupt -> (Chan (PID, p2f), Chan (PID, f2p)) -> (Chan a2f, Chan f2a) -> (Chan z2f, Chan f2z) -> (MonadFunctionality m => Functionality p2f f2p a2f f2a z2f f2z m) -> m ()
runFunctionality sid crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) f =
  let ?sid = sid
      ?crupt = crupt in f (p2f, f2p) (a2f, f2a) (z2f, f2z)


{-- Party class --}
type MonadProtocol m =
   (MonadITM m,
    ?sid :: SID,
    ?pid :: PID)

type Protocol z2p p2z f2p p2f m = MonadProtocol m => (Chan z2p, Chan p2z) -> (Chan f2p, Chan p2f) -> m ()

runProtocol :: MonadITM m => SID -> PID -> (Chan z2p, Chan p2z) -> (Chan f2p, Chan p2f) -> (MonadProtocol m => Protocol z2p p2z f2p p2f m) -> m ()
runProtocol sid pid (z2p, p2z) (f2p, p2f) pi =
  let ?sid = sid
      ?pid = pid in pi (z2p, p2z) (f2p, p2f)


{-- Adversary Class --}
type MonadAdversary m =
  (MonadITM m,
   ?sid :: SID,
   ?crupt :: Crupt,
   ?pass :: m ())

type Adversary z2a a2z f2p p2f f2a a2f m = MonadAdversary m => (Chan z2a, Chan a2z) -> (Chan (PID, f2p), Chan (PID, p2f)) -> (Chan f2a, Chan a2f) -> m ()

runAdversary :: MonadITM m => SID -> Crupt -> Chan () -> (Chan z2a, Chan a2z) -> (Chan (PID, f2p), Chan (PID, p2f)) -> (Chan f2a, Chan a2f) -> (MonadAdversary m => Adversary z2a a2z f2p p2f f2a a2f m) -> m ()
runAdversary sid crupt passer (z2a, a2z) (p2a, a2p) (f2a, a2f) a =
  let ?sid = sid
      ?crupt = crupt
      ?pass = writeChan passer () in a (z2a, a2z) (p2a, a2p) (f2a, a2f)


{-- Environment Class --}
type MonadEnvironment m =
  (MonadITM m,
   ?pass :: m ())


type Environment p2z z2p a2z z2a f2z z2f outz m = MonadEnvironment m => Chan SttCrupt_SidCrupt -> (Chan (PID, p2z), Chan (PID, z2p)) -> (Chan a2z, Chan z2a) -> (Chan f2z, Chan z2f) -> Chan () -> Chan outz -> m ()


runEnvironment :: MonadITM m => Chan () -> Chan SttCrupt_SidCrupt -> (Chan (PID, p2z), Chan (PID, z2p)) -> (Chan a2z, Chan z2a) -> (Chan f2z, Chan z2f) -> Environment p2z z2p a2z z2a f2z z2f outz m -> m outz
runEnvironment passer sidcrupt (p2z, z2p) (a2z, z2a) (f2z, z2f) z = do
  pump <- newChan
  outp <- newChan
  let ?pass = writeChan passer () in
    fork $ z sidcrupt (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  c <- multiplex passer outp
  let _run = do
        writeChan pump ()
        o <- readChan c
        case o of 
          Left  () -> _run
          Right a  -> return a in _run


{- UC Experiments -}
execUC
  :: MonadITM m =>
       (forall m. MonadEnvironment m => Environment p2z z2p a2z z2a f2z z2f outz m)
       -> (forall m. MonadProtocol m => Protocol z2p p2z f2p p2f m)
       -> (forall m. MonadFunctionality m => Functionality p2f f2p a2f f2a z2f f2z m)
       -> (forall m. MonadAdversary m => Adversary z2a a2z f2p p2f f2a a2f m)
       -> m outz
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

  pass <- newChan
  
  fork $ do
    -- First, wait for the environment to choose an sid
    SttCrupt_SidCrupt sid crupt <- readChan z2exec

    fork $ runFunctionality sid crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) f
    fork $ partyWrapper sid crupt (z2p, p2z) (f2p, p2f) (a2p, p2a) p
    fork $ runAdversary sid crupt pass (z2a, a2z) (p2a, a2p) (f2a, a2f) a
    return ()

  runEnvironment pass z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) z


data SttCrupt_SidCrupt = SttCrupt_SidCrupt SID Crupt deriving Show

data SttCruptZ2A a b = SttCruptZ2A_A2P (PID, a) | SttCruptZ2A_A2F b deriving Show
data SttCruptA2Z a b = SttCruptA2Z_P2A (PID, a) | SttCruptA2Z_F2A b deriving Show


{- Protocol party wrapper -}

partyWrapper :: MonadITM m => SID -> Crupt -> (Chan (PID, z2p), Chan (PID, p2z)) -> (Chan (PID, f2p), Chan (PID, p2f)) -> (Chan (PID, p2f), Chan (PID, f2p)) -> (MonadProtocol m => Protocol z2p p2z f2p p2f m) -> m ()
partyWrapper sid crupt (z2p, p2z) (f2p, p2f) (a2p, p2a) p = do
  -- Store a table that maps each PID to a channel (z2p,f2p,a2p) used
  -- to communicate with that instance of the protocol
  z2pid <- newIORef empty
  f2pid <- newIORef empty

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
        fork $ runProtocol sid pid z f p
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
    if member pid crupt then error "env sent to corrupted party!" else return undefined
    --liftIO $ putStrLn $ "party wrapper z->p received"
    _pid <- getPid z2pid pid
    writeChan _pid m 
    
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
    if not $ member pid crupt then error "tried to send corrupted!" else return undefined
    writeChan p2f (pid, m)

  return ()



{----------------------------
 Default / Ideal / Dummy  protocols and functionalities
 ----------------------------}

dummyFunctionality (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  fork $ forever $ do
    (pid, m) <- readChan p2f
    -- liftIO $ putStrLn $ "F: [" ++ pid ++ "] " ++ show m
    writeChan (f2p) (pid, m)
  fork $ forever $ do
    m :: String <- readChan a2f
    liftIO $ putStrLn $ "F: A sent " ++ m
    writeChan (f2a) $ m
  return ()

idealProtocol (z2p, p2z) (f2p, p2f) = do
  fork $ forever $ do
    m <- readChan z2p
    --liftIO $ putStrLn $ "idealProtocol received from z2p " ++ pid
    writeChan p2f m
  fork $ forever $ do
    m <- readChan f2p
    --liftIO $ putStrLn $ "idealProtocol received from f2p " ++ pid
    writeChan p2z m
  return ()

-- dummyAdversary :: MonadAdversary m => Adversary (SttCruptZ2A b d) (SttCruptA2Z a c) a b c d m
dummyAdversary (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >>= \mf -> 
      case mf of
        SttCruptZ2A_A2F b        -> writeChan a2f b
        SttCruptZ2A_A2P (pid, m) -> writeChan a2p (pid, m)
  fork $ forever $ readChan f2a >>= writeChan a2z . SttCruptA2Z_F2A
  fork $ forever $ readChan p2a >>= writeChan a2z . SttCruptA2Z_P2A
  return ()

voidAdversary crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >> ?pass
  fork $ forever $ readChan f2a >> ?pass
  fork $ forever $ readChan p2a >> ?pass
  return ()


testEnv z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do

  -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("sid1","") empty

  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    --writeChan outp ()
    ?pass

  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m
    writeChan outp "environment output: 1"

  () <- readChan pump
  liftIO $ putStrLn "pump"
  b <- ?getBit
  if b then
      writeChan z2p ("Alice", show "0")
  else
      writeChan z2p ("Bob", show "1")

  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F "ok"

testExec = runITMinIO 120 $ execUC testEnv idealProtocol dummyFunctionality dummyAdversary


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
    if member pid crupt then error "p sent from corrupted party!" else return undefined
    getPid f2pid pid >>= flip writeChan m

  -- Routing between z and rho
  fork $ forever $ do
    (pid, m) <- readChan z2pZ
    if member pid crupt then error "env (z) sent to corrupted party!" else return undefined
    getPid z2pid pid >>= flip writeChan m

