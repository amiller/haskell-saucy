 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, PartialTypeSignatures, RankNTypes
  
  #-} 

import Control.Concurrent.MonadIO
import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map
import Control.Monad (forever)
import Control.Monad.Trans.Reader
import ProcessIO
import StaticCorruptions
import OptionallyLeak

-- Commitment is impossible to realize in the standard model

data ComP2F a = ComP2F_Commit a | ComP2F_Open deriving Show
data ComF2P a = ComF2P_OK | ComF2P_Commit   | ComF2P_Open a deriving Show
data ComF2A a = ComF2A_Commit   | ComF2A_Open a deriving Show

fDirect crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid
  fork $ forever $ do
    (pid, m) <- readChan p2f
    case () of 
      _ | pid == pidS -> writeChan f2p (pidR, m)
      _ | pid == pidR -> writeChan f2p (pidS, m)
  fork $ forever $ do -- Tie off the z2f channel
    (v :: Void) <- readChan z2f
    writeChan f2z v
  fork $ forever $ do -- Tie off the a2f channel
    (v :: Void) <- readChan a2f
    writeChan f2a v
  return ()

fCom dbg leak optionally crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid

  s2f <- newChan
  fork $ forever $ do
    (pid, m) <- readChan p2f
    case () of _ | pid == pidS -> writeChan s2f m

  -- Receive a value from the sender
  ComP2F_Commit x <- readChan s2f
  -- Debug option:
  case dbg of Nothing -> return ()
              Just d -> writeChan d x
  leak ComF2A_Commit
  optionally $ do
    -- Optionally inform the receiver
    writeChan f2p (pidR, ComF2P_Commit)
  writeChan f2p (pidS, ComF2P_OK)

  -- Receive the opening instruction from the sender
  ComP2F_Open <- readChan s2f
  leak (ComF2A_Open x)
  optionally $ do
    -- Optionally reveal to the receiver
    writeChan f2p (pidR, ComF2P_Open x)
  writeChan f2p (pidS, ComF2P_OK)

testEnvCommit z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestCommit", show ("Alice", "Bob", ("","")))
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    (pid,x) <- readChan p2z
    liftIO $ putStrLn $ "Z: party [" ++ pid ++ "] sent " ++ show x
    pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: adv sent " ++ show "[nothing]" --m
    pass

  -- Have Alice commit to a bit
  () <- readChan pump
  b <- getBit
  writeChan z2p ("Alice", ComP2F_Commit b)

  -- Deliver the first message
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- Have Alice open the message
  () <- readChan pump
  writeChan z2p ("Alice", ComP2F_Open)
            
  -- Deliver the second message
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  return ()

testCommit :: IO _
testCommit = runRand $ execUC testEnvCommit (idealProtocol) (runOptLeak $ fCom Nothing) dummyAdversary

envComZ1 alice2bob bob2alice z2exec (p2z, z2p :: Chan (PID, ComP2F _)) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestCommitZ1", show ("Alice", "Bob", ("","")))

  -- In Z1, Alice is corrupted
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Alice",())])

  -- Alert when Bob receives a "Commit" message
  fork $ forever $ do
    (pid, m) <- readChan p2z
    case m of
      ComF2P_Commit | pid == "Bob" -> writeChan outp ComF2P_Commit
      ComF2P_Open b | pid == "Bob" -> undefined

  -- Force Z2F to be Void
  fork $ forever $ do
    (a :: Void) <- readChan f2z 
    writeChan z2f a

  -- Forward messages from honest Bob to the outside Alice

  fork $ forever $ do
    mf <- readChan a2z
    case mf of
      SttCruptA2Z_P2A (pid, m) | pid == "Alice" -> do
                     liftIO $ putStrLn $ "Z1: intercepted bob2alice"
                     writeChan bob2alice m
      SttCruptA2Z_F2A (v :: Void) -> writeChan z2a (SttCruptZ2A_A2F v)

  -- Forward messages from the "outside" Alice to the honest Bob
  fork $ forever $ do
    m <- readChan alice2bob
    writeChan z2a $ SttCruptZ2A_A2P ("Alice", m)

  return ()

envComZ2 :: Bool -> (MonadDefault m, MonadRand m) =>
     (Crupt -> _ -> _ -> _ -> (forall m1. HasFork m1 => m1 ()))
     -> (PID -> _ -> _ -> (forall m2. HasFork m2 => m2 ()))
     -> Chan SttCrupt_SidCrupt
     -> (Chan ([Char], t5), Chan ([Char], ComP2F Bool))
     -> (Chan (SttCruptA2Z a1 t6), t2)
     -> (t3, t4)
     -> Chan ()
     -> Chan (Bool, Bool)
     -> m ()
envComZ2 option s p z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestCommitZ2", show ("Alice", "Bob", ("","")))
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Bob",())])

  alice2bob <- newChan 
  bob2alice <- newChan
  alert <- newChan

  fork $ forever $ do
    (pid,x) <- readChan p2z
    liftIO $ putStrLn $ "Z2: party [" ++ pid ++ "] sent " -- ++ show x
    pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z2: adv sent " ++ show "[nothing]" --m
    case m of 
      -- Forward messages from Alice2Bob to internal Z1
      SttCruptA2Z_P2A (pid, m) | pid == "Bob" -> do
                     liftIO $ putStrLn $ "Z: corrupt Bob received msg"
                     writeChan alice2bob m


  -- Have Alice commit to a bit
  () <- readChan pump
  b <- getBit
  writeChan z2p ("Alice", ComP2F_Commit b)

  if option then do
              -- Run one copy of the experiment with ideal
              dbg <- newChan
              fork $ do
                   execUC (envComZ1 alice2bob bob2alice) (idealProtocol) (runOptLeak $ fCom $ Just dbg) s
                   return ()
              b' <- readChan dbg
              writeChan outp (b, b')
  else
      -- Run one copy of the experiment with real protocol
      do 
        ComF2P_Commit <- execUC (envComZ1 alice2bob bob2alice) (p) (fDirect) dummyAdversary
        writeChan outp (b, b)

  return ()

testEnvComZ2TestIdeal :: Bool -> (Crupt -> _ -> _ -> _ -> forall m1. HasFork m1 => m1 ()) -> (PID -> _ -> _ -> (forall m2. HasFork m2 => m2 ())) -> IO _
testEnvComZ2TestIdeal b s p = runRand $ execUC (envComZ2 b s p) (idealProtocol) (runOptLeak $ fCom Nothing) s


testEnvComZ2TestReal :: Bool -> (Crupt -> _ -> _ -> _ -> forall m1. HasFork m1 => m1 ()) -> (PID -> _ -> _ -> (forall m2. HasFork m2 => m2 ())) -> IO _
testEnvComZ2TestReal b s p = runRand $ execUC (envComZ2 b s p) (p) (fDirect) dummyAdversary

-- [Experiment 0]
-- We can show that this experiment returns b
expt0 s p = testEnvComZ2TestIdeal False

-- [Experiment 1]



{- Commitment is impossible in the plain model
      and in a model with communications between sender and receiver
   Theorem 6 from 
     Universally Composable Commitments
     https://eprint.iacr.org/2001/055 

   Suppose F_com is realizable.
   Then there is a protocol p, and a simulator s (parameterized by adversary a), such that
     forall a z. execUC z p a dF ~ execUC z dP (s a) fCom 

   We will show this is impossible, by constructing a distinguisher z and adversary a, such that
     let (z, a) = zbad p s
     execUC z p a dummyF ~/~ execUC z idealP (s a) fCom

 -}
