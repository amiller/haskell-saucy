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

data AuthF2P a = AuthF2P_OK | AuthF2P_Msg a

fAuth leak optionally crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid
  fork $ forever $ do
    (pid, m) <- readChan p2f
    leak (pid, m)
    optionally $ do
      case () of 
        _ | pid == pidS -> writeChan f2p (pidR, AuthF2P_Msg m)
        _ | pid == pidR -> writeChan f2p (pidS, AuthF2P_Msg m)
    writeChan f2p (pid, AuthF2P_OK)
  fork $ forever $ do -- Tie off the z2f channel
    (v :: Void) <- readChan z2f
    writeChan f2z v
  fork $ forever $ do -- Tie off the a2f channel
    (v :: Void) <- readChan a2f
    writeChan f2a v
  return ()

fComDbg dbg = fCom_ (Just dbg)
fCom = fCom_ Nothing -- Without debug
fCom_ dbg leak optionally crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
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
  case dbg of 
    Just d -> writeChan d x
    Nothing -> do
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

envComBenign z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestCommit", show ("Alice", "Bob", ("","")))
  writeChan z2exec $ SttCrupt_SidCrupt sid empty

  -- Flip a random bit
  () <- readChan pump
  b <- getBit

  fork $ forever $ do
    (pid,x) <- readChan p2z
    liftIO $ putStrLn $ "Z: party [" ++ pid ++ "] recvd " -- ++ show x
    case x of
      ComF2P_Open b' | pid == "Bob" -> writeChan outp (b, b')
      _ -> pass
  fork $ forever $ do
    _ <- readChan a2z
    undefined

  -- Have Alice comit to a bit
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


      
testComBenignIdeal :: _ -> IO _
testComBenignIdeal s = runRand $ execUC envComBenign (idealProtocol) (runOptLeak $ fCom) s

testComBenignReal :: _ -> IO _
testComBenignReal p = runRand $ execUC envComBenign (p) (runOptLeak fAuth) (dummyAdversary)



{- Commitment is impossible in the plain model
   (and even in a model with direct communications 
    between sender and receiver)
   Theorem 6 from 
     Universally Composable Commitments
     https://eprint.iacr.org/2001/055 

   Suppose F_com is realizable.
   Then there is a protocol p, and a simulator s (parameterized by adversary a), such that
     forall a z. execUC z p a dF ~ execUC z dP (s a) fCom 

   We will show this is impossible, by constructing a distinguisher z such that
     execUC z p dummyA fAuth ~/~ execUC z idealP s fCom

 -}

envComZ1 alice2bob bob2alice z2exec (p2z, z2p :: Chan (PID, ComP2F _)) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestCommitZ1", show ("Alice", "Bob", ("","")))
            
  -- In Z1, Alice is corrupted
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Alice",())])

  -- Wait for first message
  () <- readChan pump

  -- Alert when Bob receives a "Commit" message
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z1: party [" ++ pid ++ "] recv " -- ++ show x
    case m of
      ComF2P_Commit | pid == "Bob" -> do writeChan outp ComF2P_Commit
      _ -> pass

  -- Force Z2F to be Void
  fork $ forever $ do
    (a :: Void) <- readChan f2z 
    writeChan z2f a

  -- Forward messages from honest Bob to the outside Alice
  fork $ forever $ do
    mf <- readChan a2z
    case mf of
      SttCruptA2Z_P2A (pid, m) | pid == "Bob" -> do
                     liftIO $ putStrLn $ "Z1: intercepted bob2alice"
                     undefined
                     writeChan bob2alice m
      _ -> pass
      --SttCruptA2Z_F2A (Optional :: Void) -> writeChan z2a (SttCruptZ2A_A2F v)

  -- Forward messages from the "outside" Alice to the honest Bob
  fork $ forever $ do
    m <- readChan alice2bob
    liftIO $ putStrLn "Z1: providing message on behalf of Alice"
    writeChan z2a $ SttCruptZ2A_A2P ("Alice", m)

  -- Deliver the first message
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  -- Wait for second message
  () <- readChan pump
  -- Deliver the first message
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  return ()

-- envComZ2 :: Bool -> (MonadDefault m, MonadRand m) =>
--      (Crupt -> _ -> _ -> _ -> (forall m1. (HasFork m1, MonadSID m1) => m1 ()))
--      -> (PID -> _ -> _ -> (forall m2. (HasFork m2, MonadSID m2) => m2 ()))
--      -> Chan SttCrupt_SidCrupt
--      -> (Chan ([Char], t5), Chan ([Char], ComP2F Bool))
--      -> (Chan (SttCruptA2Z (AuthF2P aa) t6), t2)
--      -> (t3, t4)
--      -> Chan ()
--      -> Chan (Bool, Bool)
--      -> m ()
envComZ2 option s p z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestCommitZ2", show ("Alice", "Bob", ("","")))
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [("Bob",())])

  alice2bob <- newChan 
  bob2alice <- newChan
  alert <- newChan

  -- Pick a random bit
  () <- readChan pump
  b <- getBit

  fork $ forever $ do
    (pid,x) <- readChan p2z
    liftIO $ putStrLn $ "Z2: party [" ++ pid ++ "] recv " -- ++ show x
    pass

  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z2: adv sent " ++ show "[nothing]" --m
    case m of 
      -- Forward messages from Alice2Bob to internal Z1
      SttCruptA2Z_P2A (pid, AuthF2P_Msg m) | pid == "Bob" -> do
                     liftIO $ putStrLn $ "Z2: corrupt Bob received msg"
                     writeChan alice2bob m

  if option then do
              -- Run one copy of the experiment with ideal
              --liftIO $ putStrLn $ "Z2: running ideal Z1!"
              dbg <- newChan
              fork $ do
                   -- Marker 1
                   execUC (envComZ1 alice2bob bob2alice) (idealProtocol) (runOptLeak $ fComDbg dbg) s
                   return ()
              fork $ do 
                   b' <- readChan dbg
                   writeChan outp (b, b')
  else do
    -- Run one copy of the experiment with real protocol
    --liftIO $ putStrLn $ "Z2: running real Z1!"
    fork $ do
         -- Marker 2
         ComF2P_Commit <- execUC (envComZ1 alice2bob bob2alice) (p) (runOptLeak fAuth) dummyAdversary
         writeChan outp (b, b)

  -- Have Alice commit to a bit
  writeChan z2p ("Alice", ComP2F_Commit b)

  -- Deliver the first message
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  return ()

testComZ2TestIdeal :: Bool -> (Crupt -> _ -> _ -> _ -> forall m1. (HasFork m1, MonadSID m1, MonadRand m1) => m1 ()) -> (PID -> _ -> _ -> (forall m2. (HasFork m2, MonadSID m2) => m2 ())) -> IO _
testComZ2TestIdeal b s p = runRand $ execUC (envComZ2 b s p) (idealProtocol) (runOptLeak $ fCom) s


testComZ2TestReal :: Bool -> (Crupt -> _ -> _ -> _ -> forall m1. (HasFork m1, MonadSID m1, MonadRand m1) => m1 ()) -> (PID -> _ -> _ -> (forall m2. (HasFork m2, MonadSID m2) => m2 ())) -> IO _
testComZ2TestReal b s p = runRand $ execUC (envComZ2 b s p) (p) (runOptLeak fAuth) dummyAdversary

-- [Experiment 0]
-- This experiment must output (b,b) for any s that makes progress
expt0 s = testComBenignIdeal s
expt0' = expt0 dummyAdversary

-- [Experiment 1]
-- By assuming to the contrary that p realizes fCom, this must also make output (b,b)
expt1 p = testComBenignReal p
expt1B = expt1 protBindingNotHiding
expt1H = expt1 protHiding

-- [Experiment 2]
-- This experiment is *identical* to expt1 by observational equivalence
-- Although Z2 corrupts Bob, it forwards messages from a correct execution of Bob's protocol.
-- Note that s is ignored entirely
expt2 = testComZ2TestReal False
expt2B = expt2 simBindingNotHiding protBindingNotHiding
expt2H = expt2 simHiding protHiding

-- [Experiment 3]
-- This experiment is the result of replacing the internal real Z1
-- with the internal ideal Z1. Assuming s simulates p, 
-- these are indistinguishable
expt3 = testComZ2TestReal True
expt3B = expt3 simBindingNotHiding protBindingNotHiding
expt3H = expt3 simHiding protHiding 
-- expt3H: Uncorrelated, since the assumption is violated by the Hiding-Not-Binding protocol

-- [Experiment 4]
-- This experiment is the ideal analogue to expt3
-- However, here (b,b') must be *uncorrelated*. This is because
-- sim is simply not given any access to b.
expt4 = testComZ2TestIdeal True
expt4B = expt4 simBindingNotHiding protBindingNotHiding
expt4H = expt4 simHiding protHiding




-- Concrete examples of a (bad) protocol and an ineffective (but type-checking) simulator

data BindingNotHiding_Msg a = BNH_Commit a | BNH_Open deriving Show
protBindingNotHiding pid (z2p, p2z) (f2p, p2f) = do
  -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid
  case () of 
    _ | pid == pidS -> do
            ComP2F_Commit b <- readChan z2p
            writeChan p2f $ BNH_Commit b
            AuthF2P_OK <- readChan f2p
            writeChan p2z ComF2P_OK
            ComP2F_Open <- readChan z2p
            writeChan p2f $ BNH_Open
            AuthF2P_OK <- readChan f2p
            writeChan p2z ComF2P_OK
    _ | pid == pidR -> do
            AuthF2P_Msg (BNH_Commit b) <- readChan f2p
            writeChan p2z ComF2P_Commit
            AuthF2P_Msg BNH_Open <- readChan f2p
            writeChan p2z $ ComF2P_Open b          
  return ()

simBindingNotHiding crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid

  a2s <- newChan
  f2r <- newChan
  f2s <- newChan

  fork $ forever $ do
    mf <- readChan z2a
    case mf of SttCruptZ2A_A2P (pid, m) | pid == pidS -> do
                     liftIO $ putStrLn $ "sim: sender " ++ show m
                     writeChan a2s (m :: BindingNotHiding_Msg Bool)
               SttCruptZ2A_A2P (pid, m) | pid == pidR -> do
                     undefined -- this shouldn't happen
               SttCruptZ2A_A2F (OptionalA2F_Deliver 0) -> do
                     liftIO $ putStrLn $ "sim: deliver"
                     writeChan a2f $ OptionalA2F_Deliver 0
  fork $ forever $ do
    (pid, m) <- readChan p2a
    case () of _ | pid == pidS -> writeChan f2s m
               _ | pid == pidR -> writeChan f2r m

  if member pidS crupt then do
      fork $ do
        -- Handle committing
        (BNH_Commit b) <- readChan a2s
        liftIO $ putStrLn $ "sim: writing p2f_Commit"
        writeChan a2p (pidS, ComP2F_Commit b)
        ComF2P_OK <- readChan f2s
        writeChan a2z $ SttCruptA2Z_P2A (pidS, AuthF2P_OK)

        -- Handle opening
        (BNH_Open) <- readChan a2s
        writeChan a2p (pidS, ComP2F_Open)
        ComF2P_OK <- readChan f2s
        return ()
      return ()
  else return ()
  if member pidR crupt then do
      fork $ do
        -- Handle delivery of commitment
        ComF2P_Commit <- readChan f2r 
        liftIO $ putStrLn $ "simCom: received Commit"
        -- Poor simulation (it's always 0)
        writeChan a2z $ SttCruptA2Z_P2A (pidR, AuthF2P_Msg (BNH_Commit False))
        -- Handle delivery of opening
        ComF2P_Open b' <- readChan f2r
        writeChan a2z $ SttCruptA2Z_P2A (pidR, AuthF2P_Msg (BNH_Open))
      return ()
  else return ()
  return ()


data Hiding_Msg a = Hiding_Commit | Hiding_Open a deriving Show
protHiding pid (z2p, p2z) (f2p, p2f) = do
  -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid
  case () of 
    _ | pid == pidS -> do
            ComP2F_Commit b <- readChan z2p
            writeChan p2f $ Hiding_Commit
            AuthF2P_OK <- readChan f2p
            writeChan p2z ComF2P_OK
            ComP2F_Open <- readChan z2p
            writeChan p2f $ Hiding_Open b
            AuthF2P_OK <- readChan f2p
            writeChan p2z ComF2P_OK
    _ | pid == pidR -> do
            AuthF2P_Msg Hiding_Commit <- readChan f2p
            writeChan p2z ComF2P_Commit
            AuthF2P_Msg (Hiding_Open b) <- readChan f2p
            writeChan p2z $ ComF2P_Open b          
  return ()


simHiding crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid

  a2s <- newChan
  f2r <- newChan
  f2s <- newChan

  fork $ forever $ do
    mf <- readChan z2a
    case mf of SttCruptZ2A_A2P (pid, m) | pid == pidS -> do
                     liftIO $ putStrLn $ "sim: sender " ++ show m
                     writeChan a2s (m :: Hiding_Msg Bool)
               SttCruptZ2A_A2F (OptionalA2F_Deliver 0) -> do
                     liftIO $ putStrLn $ "sim: deliver"
                     writeChan a2f $ OptionalA2F_Deliver 0
  fork $ forever $ do
    (pid, m) <- readChan p2a
    case () of _ | pid == pidS -> writeChan f2s m
               _ | pid == pidR -> writeChan f2r m

  if member pidS crupt then do
      fork $ do
        -- Handle committing
        Hiding_Commit <- readChan a2s
        -- Can't simulate very well - generate a random bit
        b <- getBit
        liftIO $ putStrLn $ "sim: writing p2f_Commit"
        writeChan a2p (pidS, ComP2F_Commit b)
        ComF2P_OK <- readChan f2s
        writeChan a2z $ SttCruptA2Z_P2A (pidS, AuthF2P_OK)

        -- Handle opening
        (Hiding_Open b') <- readChan a2s
        writeChan a2p (pidS, ComP2F_Open)
        ComF2P_OK <- readChan f2s
        return ()
      return ()
  else return ()
  if member pidR crupt then do
      fork $ do
        -- Handle delivery of commitment
        ComF2P_Commit <- readChan f2r 
        liftIO $ putStrLn $ "simCom: received Commit"
        -- Easy to simulate
        writeChan a2z $ SttCruptA2Z_P2A (pidR, AuthF2P_Msg Hiding_Commit)
        -- Handle delivery of opening
        ComF2P_Open b <- readChan f2r
        writeChan a2z $ SttCruptA2Z_P2A (pidR, AuthF2P_Msg$Hiding_Open b)
      return ()
  else return ()
  return ()



-- Positive result (needs Random Oracle)
data RoP2F a = RoP2F a
data RoF2P   = RoF2P Int
fRO (p2f, f2p) = do
  table <- newIORef Map.empty
  fork $ forever $ do
    (pid, RoP2F m) <- readChan p2f
    tbl <- readIORef table
    if member (show m) tbl then
        let Just h = Map.lookup (show m) tbl in
        writeChan f2p (pid, RoF2P h)
    else do
        h <- getNbits 120 -- generate a random string
        modifyIORef table (Map.insert (show m) h)
        writeChan f2p (pid, RoF2P h)
  return ()

data AuthRoP2F a b = AuthRoP2F_Auth a | AuthRoP2F_Ro b
data AuthRoF2P a   = AuthRoF2P_Auth a | AuthRoF2P_Ro RoF2P
fAuthRO leak optionally crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  p2fro <- newChan
  p2fauth <- newChan
  f2pro <- wrapWrite (\(pid,m) -> (pid,AuthRoF2P_Ro m)) f2p
  f2pauth <- wrapWrite (\(pid,m) -> (pid, AuthRoF2P_Auth m)) f2p

  fork $ forever $ do
    (pid, mf) <- readChan p2f
    case mf of
      AuthRoP2F_Ro m   -> writeChan p2fro (pid, m)
      AuthRoP2F_Auth m -> writeChan p2fauth (pid, m)

  fork $ fAuth leak optionally crupt (p2fauth, f2pauth) (a2f, f2a) (z2f, f2z)
  fork $ fRO (p2fro, f2pro)
  return ()

data ProtComm_Msg a = ProtComm_Commit Int | ProtComm_Open Int a deriving Show
protComm pid (z2p, p2z) (f2p, p2f) = do
    -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid
  case () of 
    _ | pid == pidS -> do
            -- Wait for commit instruction
            ComP2F_Commit b <- readChan z2p
            -- Generate the blinding
            nonce :: Int <- getNbits 120
            -- Query the random oracle
            writeChan p2f $ AuthRoP2F_Ro (RoP2F (nonce, b))
            AuthRoF2P_Ro (RoF2P h) <- readChan f2p
            writeChan p2f $ AuthRoP2F_Auth (ProtComm_Commit h)
            AuthRoF2P_Auth AuthF2P_OK <- readChan f2p
            writeChan p2z ComF2P_OK

            -- Wait for open instruction
            ComP2F_Open <- readChan z2p
            writeChan p2f $ AuthRoP2F_Auth (ProtComm_Open nonce b)
            AuthRoF2P_Auth AuthF2P_OK <- readChan f2p
            writeChan p2z ComF2P_OK

    _ | pid == pidR -> do
            AuthRoF2P_Auth (AuthF2P_Msg (ProtComm_Commit h)) <- readChan f2p
            writeChan p2z ComF2P_Commit
            AuthRoF2P_Auth (AuthF2P_Msg (ProtComm_Open nonce b)) <- readChan f2p
            -- Query the RO 
            writeChan p2f $ AuthRoP2F_Ro (RoP2F (nonce, b))
            AuthRoF2P_Ro (RoF2P h') <- readChan f2p
            if not (h' == h) then fail "hash mismatch" else return ()

            -- Output
            writeChan p2z $ ComF2P_Open b

simComm crupt (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  -- Parse sid as defining two players
  (_,sid) <- getSID
  let (pidS :: PID, pidR :: PID, ssid :: SID) = read sid

  a2s <- newChan
  f2r <- newChan
  f2s <- newChan

  fork $ forever $ do
    mf <- readChan z2a
    case mf of SttCruptZ2A_A2P (pid, m) | pid == pidS -> do
                     liftIO $ putStrLn $ "sim: sender " ++ show m
                     writeChan a2s (m :: Hiding_Msg Bool)
               SttCruptZ2A_A2F (OptionalA2F_Deliver 0) -> do
                     liftIO $ putStrLn $ "sim: deliver"
                     writeChan a2f $ OptionalA2F_Deliver 0
  fork $ forever $ do
    (pid, m) <- readChan p2a
    case () of _ | pid == pidS -> writeChan f2s m
               _ | pid == pidR -> writeChan f2r m

  -- Internalize the RO!
  table <- newIORef Map.empty -- map x to h(x) 
  backtable <- newIORef Map.empty -- map h(x) to x

  if member pidS crupt then do
      fork $ do

        -- Handle committing
        Hiding_Commit <- readChan a2s
        -- Can't simulate very well - generate a random bit
        b <- getBit
        liftIO $ putStrLn $ "sim: writing p2f_Commit"
        writeChan a2p (pidS, ComP2F_Commit b)
        ComF2P_OK <- readChan f2s
        writeChan a2z $ SttCruptA2Z_P2A (pidS, AuthF2P_OK)

        -- Handle opening
        (Hiding_Open b') <- readChan a2s
        writeChan a2p (pidS, ComP2F_Open)
        ComF2P_OK <- readChan f2s
        return ()
      return ()
  else return ()
  if member pidR crupt then do
      fork $ do
        -- Handle delivery of commitment
        ComF2P_Commit <- readChan f2r 
        liftIO $ putStrLn $ "simCom: received Commit"
        -- Easy to simulate
        writeChan a2z $ SttCruptA2Z_P2A (pidR, AuthF2P_Msg Hiding_Commit)
        -- Handle delivery of opening
        ComF2P_Open b <- readChan f2r
        writeChan a2z $ SttCruptA2Z_P2A (pidR, AuthF2P_Msg$Hiding_Open b)
      return ()
  else return ()
  return ()


testComBenignRoReal :: IO _
testComBenignRoReal = runRand $ execUC envComBenign (protComm) (runOptLeak fAuthRO) (dummyAdversary)

testComBenignRoIdeal :: IO _
testComBenignRoIdeal = runRand $ execUC envComBenign (idealProtocol) (runOptLeak fCom) simComm


--testComZ2RoReal :: IO _
--testComZ2RoReal = runRand $ execUC  (envComZ2 False simComm protComm) (protComm) (runOptLeak fAuthRO) (dummyAdversary)

--testComZ2RoIdeal :: IO _
--testComZ2RoIdeal = runRand $ execUC (envComZ2 False simComm protComm) (idealProtocol) (runOptLeak fCom) simComm
