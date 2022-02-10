{-# LANGUAGE Rank2Types, ImplicitParams, ConstraintKinds
  #-} 

{- Haskell-SaUCy Process Model

   This defines a model of probabilistic, polynomial time, channel
   passing processes. It is similar in spirit to the Interactive Turing
   Machines model (ITMs), and to the equivalent processes in ILC-SaUCy,

   Instead of tapes (in ITMs), or ILC channels, we use the channels
   provided by the Haskell library Control.Concurrent.

   But note well that the Haskell type system is only used to enforce
   a *subset* of the constraints enforced by ILC. So you can represent
   computations here that wouldn't be permitted in ILC.

   In particular, this library *cannot* guarantee that your program
   respects:
   - 1) no duplication of "read end" of a channel...
   - 2) no duplication of the "write token"...
   - 3) no passing of channels over channels...
   - 4) no duplication of "import tokens"
   So you are on your own to make sure these are respected.

   The Haskell-SaUCy process model provides several programming
   abstractions, added to the syntax through a Monad typeclass,
   MonadITM. These are:
   1. Random coin flips
   2. Import tokens, and ticks used to bound running time
   3. A security parameter ?secParam

   The reason for the Monad typeclass is that a well-defined ITM
   must be parametric in each of these features:
      type ITM a = (forall m. MonadITM m => m a)
   This is important for "simulating a process in a sandbox", which is
   a frequently occurring proof technique. In particular, "overriding"
   the random coin flips is useful in rewinding proofs, since the random
   bits used by the "sandboxed" process can be recorded and replayed.

   In SaUCy we want to judge processes as being polynomial time,
   where polynomial time is related to the security parameter,
   the import tokens, and a computation counter. When simulating
   in a sandbox, the import tokens can be overridden, but not the ticks.
 -}

module ProcessIO where

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM, forM_, replicateM_)
import Data.IORef.MonadIO
import System.Random
import Data.Map.Strict hiding (drop,splitAt)

{-- Typeclass for ITMs --}

type MonadITM m = (HasFork m,
                   ?getBit :: m Bool,
                   ?secParam :: Int,
                   ?getTokens :: m Int,
                   ?tick :: m ())

getBit :: MonadITM m => m Bool
getBit = ?getBit
secParam :: MonadITM m => Int
secParam = ?secParam
getTokens :: MonadITM m => m Int
getTokens = ?getTokens

printEnvIdeal s = liftIO $ putStrLn $ "Z: \ESC[32m" ++ s ++ "\ESC[0m"
printEnvReal s = liftIO $ putStrLn $ "Z: \ESC[34m" ++ s ++ "\ESC[0m"

{-- Communicating over channels --}
{-- Haskell-SaUCy processes can make use of the
     writeChan
     readChan
     newChan
     fork
    features from Control.Concurrent.MonadIO. --}
wrapWrite f c = do
  d <- newChan 
  fork $ forever $ readChan d >>= writeChan c . f 
  return d

wrapRead f c = do
  d <- newChan
  fork $ forever $ readChan c >>= writeChan d . f 
  return d

-- Multiplexes two "read" channels into a single new read channel
twoplexRd :: HasFork m => Chan a -> Chan b -> m (Chan (Either a b))
twoplexRd a b = do
  c <- newChan
  fork $ forever $ readChan a >>= writeChan c . Left
  fork $ forever $ readChan b >>= writeChan c . Right
  return c

-- Multiplexes two "write" channels into a single read channel
twoplexWr :: HasFork m => Chan a -> Chan b -> m (Chan (Either a b))
twoplexWr a b = do
  c <- newChan
  fork $ forever $ do
    m <- readChan c
    case m of Left  x -> writeChan a x
              Right x -> writeChan b x
  return c

-- Demultiplexes a "read" chanenl into two separate read channels
detwoplexRd :: HasFork m => Chan (Either a b) -> m (Chan a, Chan b)
detwoplexRd ab = forever $ do
  a <- newChan
  b <- newChan
  fork $ forever $ do
    x <- readChan ab
    case x of
      Left  y -> writeChan a y
      Right y -> writeChan b y
  return (a,b)

-- Demultiplexes a "write" channel into two separate write channels
detwoplexWr :: HasFork m => Chan (Either a b) -> m (Chan a, Chan b)
detwoplexWr ab = forever $ do
  a <- newChan
  b <- newChan
  fork $ forever $ readChan a >>= writeChan ab . Left
  fork $ forever $ readChan b >>= writeChan ab . Right
  return (a,b)


{- Syntax sugar for parallel composition, returning the right value -}
(|.) :: HasFork m => m () -> m () -> m ()
p |. q = fork p >> q
infixl 1 |.


{- Example of Implicit parameters and custom Monad constraints -}
example_usesImplicitInt :: (Monad m, (?getMyIntParam :: m Int)) => m String
example_usesImplicitInt = do
   n <- ?getMyIntParam;
   return $ "My Parameter is: " ++ show n

example_runWithInt :: Monad m => Int -> ((?getMyIntParam :: m Int) => m a) -> m a
example_runWithInt n p = let ?getMyIntParam = return n in p

testImplicit1_run :: IO ()
testImplicit1_run = liftIO $ example_runWithInt 10 $ do
  example_usesImplicitInt >>= putStrLn
  example_runWithInt 20 $ do
    example_usesImplicitInt >>= putStrLn


{--------------------------------------------}
{- Implicit Parameter: Random coin flips  -}
{--------------------------------------------}
{- Processes have access to ?getBit
 -}
{- Composing machines through "sandbox" emulation often involves
   adapting the random stream. For example, for rewinding. -}
runRand :: Monad m => m Bool -> ((?getBit :: m Bool) => m a) -> m a
runRand getBit p = let ?getBit = getBit in p

{- The direct way is through access to the IO monad -}
runRandIO :: MonadIO m => ((?getBit :: m Bool) => m a) -> m a
runRandIO p = let ?getBit = (liftIO $ randomRIO (False,True)) in p


--getNbits :: (Num a, Monad m, ?getBit :: m Bool) => Int -> m a
getNbits 0 = return 0
getNbits n | n < 0 = error "negative bits?"
getNbits n = do
  b <- ?getBit
  rest <- getNbits (n-1)
  return $ 2*rest + if b then 0 else 1

get32bytes :: (Num a, Monad m, ?getBit :: m Bool) => m a
get32bytes = getNbits (32*8)

flippedRand f = let ?getBit = ?getBit >>= (return . not) in f

testRand2 :: IO Bool
testRand2 = runRandIO $ flippedRand ?getBit


{- Record/replay example (for rewinding proofs) -}

{- Run p to completion, and record the bits it takes -}
runRandRecord :: (MonadIO m, ?getBit :: m Bool) =>
  ((?getBit :: m Bool) => m a) -> m (a, [Bool])
runRandRecord p = do
  ref <- newIORef []
  let ?getBit = do
        bit <- ?getBit
        modifyIORef ref ((:) bit)
        return bit
  output <- p
  bits <- readIORef ref
  return (output, reverse bits)

{- Run p using a provided stream of bits -}
runRandReplay :: (MonadIO m, ?getBit :: m Bool) =>
  [Bool] -> ((?getBit :: m Bool) => m a) -> m a
runRandReplay bits p = do
  ref <- newIORef bits
  let ?getBit = do
        br <- readIORef ref
        let (bit : rest) = br
        writeIORef ref rest
        return bit
    in p

{- Examples -}
testRewindA :: (HasFork m, ?getBit :: m Bool) => m ()
testRewindA = do
  a1 <- get32bytes
  a2 <- get32bytes
  liftIO $ putStrLn $ "a1: " ++ show a1 ++ " a2: " ++ show a2

testRewindB :: (HasFork m, ?getBit :: m Bool) => m ()
testRewindB = do
  b1 <- get32bytes
  b2 <- get32bytes
  liftIO $ putStrLn $ "b1: " ++ show b1 ++ " b2: " ++ show b2

testRewind :: IO ()
testRewind = runRandIO $ do
  ((), bits) <- runRandRecord $ testRewindA
  runRandReplay bits $ testRewindB



{--------------------------------------------}
{- Implicit Parameter: Security Parameter   -}
{--------------------------------------------}
{- The security parameter, ?secParam, is a straightforward use
   case for implicit parameters in Haskell-SaUCy. It's assumed
   to be available when defining a protocol, functionality,
   simulator, etc., but not set concretely until runtime.
-}


{-------------------------------------------}
{- Running ITMs                           --}
{-------------------------------------------}

runITMinIO :: Int -> (forall m. MonadITM m => m a) -> IO a
runITMinIO k p = do
  let ?secParam = k in runRandIO $
    let ?getTokens = undefined in
      let ?tick = undefined in
        p


{- Examples -}

flipWrite a b = do
  x <- ?getBit
  if x then writeChan a ()
  else      writeChan b ()

counter a b = do
  ab <- twoplexWr a b
  let counter' n = do
                c <- readChan ab
                case c of 
                  Left  s -> liftIO $ putStrLn ("a" ++ show n)
                  Right s -> liftIO $ putStrLn ("b" ++ show n)
                counter' (n+1)
  counter' 0

-- Ask for a random bit, and print a message according to which one
test1 :: MonadITM m => m ()
test1 = do
  a <- newChan
  b <- newChan
  fork $ counter a b
  replicateM_ 10 $ flipWrite a b

test1run :: IO ()
test1run = do { runITMinIO 40 test1;
                threadDelay 1000}

{-- Ping Pong and channel params --}
doubler i o = do
  x <- readChan i
  writeChan o (x*2)

test2 :: MonadITM m => m ()
test2 = do
  a <- newChan
  b <- newChan
  fork $ doubler a b
  writeChan a 15
  output <- readChan b
  liftIO $ putStrLn $ "Output: " ++ show output
  return ()

test2run = runITMinIO 120 test2



{- Example of non-ILC respecting Haskell code.
 ------
 Haskell-SaUCy is a pragmatic alternative to ILC, but the type system here
 only enforces some of the requirements of the SaUCy computing model.
 In particular, this can exhibit non-deterministic concurrency if you
 parallel-compose two 
   -}

{- TODO -}

{- More Features -}



{- run-time checking of a condition or throw exception -}
require cond msg = if not cond then error msg else return ()



{-
Exploring the multiplexer options.
 --}

qEcho :: MonadITM m => (Chan a, Chan a) -> m ()
qEcho (fromOpp, toOpp) = do
  forever $ do
    x <- readChan fromOpp
    writeChan toOpp x

qUnit :: MonadITM m => (Chan p2q, Chan ()) -> m ()
qUnit (fromOpp, toOpp) = do
  forever $ do
    _ <- readChan fromOpp
    writeChan toOpp ()

pLeader (fromOpp, toOpp) = do
  writeChan toOpp 1
  _ <- readChan fromOpp
  return ()
  
-- First the setup, a generic way of running two well-matched processes.
runOpposed :: (MonadITM m => (Chan q2p, Chan p2q) -> m ()) ->
              (MonadITM m => (Chan p2q, Chan q2p) -> m ()) ->
              MonadITM m => m ()
runOpposed p q = do
   q2p <- newChan
   p2q <- newChan
   fork $ q (p2q, q2p)
   p (q2p, p2q)    -- Return when p is finished
   return () 

{--
The simple bounded multiplexer.
    Left f1 | Right f2
This is easy, we go ahead and immediately create both instances.
 -}
runMux2 :: MonadITM m => ((Chan p2qL, Chan q2pL) -> m ()) ->
                         ((Chan p2qR, Chan q2pR) -> m ()) ->
                      (Chan (Either p2qL p2qR), Chan (Either q2pL q2pR)) -> m ()
runMux2 qL qR (p2q,q2p) = do
  (p2qL,p2qR) <- detwoplexRd p2q
  (q2pL,q2pR) <- detwoplexWr q2p
  fork $ qL (p2qL, q2pL)
  fork $ qR (p2qR, q2pR)
  return ()

--myProgramA :: _
myProgramA (fromOpp, toOpp) = do
  writeChan toOpp ("test")
  x <- readChan fromOpp
  liftIO $ putStrLn $ show x
  return ()

--myProgram ::
myProgramB (fromOpp, toOpp) = do
  writeChan toOpp (Right "ok")
  mr <- readChan fromOpp
  let (Right x) = mr
  liftIO $ putStrLn $ show mr
  writeChan toOpp (Left "ok")
  mr <- readChan fromOpp
  let (Left x) = mr
  liftIO $ putStrLn $ show mr
  return ()

testOppA = runITMinIO 120 $ runOpposed myProgramA qEcho
testOppB = runITMinIO 120 $ runOpposed myProgramB (runMux2 qUnit qEcho)

{--
 The unbounded multiplexer, !q.
    We don't know in advance how many sessions there will be.

    So when receiving a new "sid" never seen before,
      create a new instance of "q".

    Route messages to and from the internally running instances.
--}

bangQ :: MonadITM m =>
              ((Chan          p2q , Chan          q2p ) -> m ()) ->
               (Chan (String, p2q), Chan (String, q2p)) -> m ()
bangQ q (p2q,q2p) = do
  -- Store a table that maps each ID to a write channel (p2q) used
  -- to send a message to the corresponding sub-instance of f
  p2qid <- newIORef empty

  -- subroutine to install a new instance
  let newSession sid = do
        liftIO $ putStrLn $ "Creating new instance [" ++ show sid ++ "]"
        -- Write end
        qq2p <- wrapWrite (\m -> (sid,m)) q2p
        -- Read end
        p2qq <- newChan
        modifyIORef p2qid $ insert sid p2qq
        fork $ q (p2qq, qq2p)
        return ()

  -- Retrieve the {q2p} writechannel by SID (or install a new one
  -- if this is the first such message)
  let getSid sid = do
        seenBefore <- return . member sid =<< readIORef p2qid
        if not seenBefore then newSession sid else return ()
        readIORef p2qid >>= return . (! sid)

  -- Route messages from (p2q) opponent to subinstances
  forever $ do
    (sid, m) <- readChan p2q
    p2qid <- getSid sid
    writeChan p2qid m


myProgramC :: MonadITM m => (Chan (String, String), Chan (String, String))-> m ()
myProgramC (fromOpp, toOpp) = do
  writeChan toOpp ("Alice", "hi alice")
  mr <- readChan fromOpp
  let ("Alice", x) = mr
  liftIO $ putStrLn $ show mr
  
  writeChan toOpp ("Bob", "ok bob")
  mr <- readChan fromOpp
  let ("Bob", x) = mr
  liftIO $ putStrLn $ show mr
  
  writeChan toOpp ("Alice", "hi a second time, alice")
  mr <- readChan fromOpp
  let ("Alice", x) = mr
  liftIO $ putStrLn $ show mr
  
  return ()

testOppC = runITMinIO 120 $ runOpposed myProgramC (bangQ qEcho)


{--
   Read (once) on either a or b, returning whichever is ready first,
   After this action returns, both channels are "available" again for
   the caller to read on.
--}

selectRead a b = do
  poll <- newChan
  a_id <- fork $ readChan a >>= writeChan poll . Left
  b_id <- fork $ readChan b >>= writeChan poll . Right
  res <- readChan poll
  killThread a_id
  killThread b_id
  return res

testSelect = runITMinIO 120 $ do
  a <- newChan
  b <- newChan
  fork  $ flipWrite a b
  res <- selectRead a b
  liftIO $ putStrLn $ show res
  fork  $ flipWrite a b
  res <- selectRead a b
  liftIO $ putStrLn $ show res  
      

{--- Counter examples.
   Why are the ILC rules defined the way they are?
   What would go wrong if we allowed race conditions?
---}

{-
   (I) In the first example, we look at the possibility of a race
   condition involving "write."

   We can't model the scheduler's choices simply as a fair probability
   distribution, since that would be an unusually strong assumption. In
   this example, only 1 out of the 2^12 possible schedules is a problem.
   But we can't justify this in the formal model.
--}

counterExampleProgram :: MonadITM m => m ()
counterExampleProgram = do
  a <- newChan
  b <- newChan
  c <- newChan
  d <- newChan

  -- This is a hardcoded sequence, so it's common knowledge
  -- (to parties as well as to any "scheduler" we imagine)
  let myFixedCode = [0,1,0,0,0,1,0,0,1,1,0,1]

  let prog (-1) _ _ _ _ = return ()
      prog n a b c d = do
        mf <- selectRead a b
        let f = case mf of Left  _ -> 0
                           Right _ -> 1
        if f == myFixedCode !! n then do
          case mf of Left  _ -> writeChan c ()
                     Right _ -> writeChan d ()
          
          prog (n-1) a b c d
        else error "The scheduler activated my trapdoor!"

  fork $ forever $ do
    writeChan a ()
    readChan c
  fork $ forever $ do
    writeChan b ()
    readChan d

  prog 11 a b c d
  
testCe1 = runITMinIO 120 $ counterExampleProgram


{-
   (II) In the second example, we look at the possibility of conveying
   secret information to the scheduler via choices.


--}
