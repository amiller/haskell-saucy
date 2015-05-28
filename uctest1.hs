{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables
  
  #-} 

{- 

 -}

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)
import Control.Monad.Reader

import System.Random

import ProcessIO

import Data.IORef.MonadIO
import Data.Map.Strict

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

  fork $ f (p2f, f2p) (a2f, f2a)
  fork $ p (z2p, p2z) (f2p, p2f) (a2p, p2a) 
  fork $ a (z2a, a2z) (p2a, a2p) (f2a, a2f)

  runUntilOutput $ z (p2z, z2p) (a2z, z2a)

-- Implement PIDs
partyWrapper p (z2p, p2z) (f2p, p2f) (a2p, p2a) = do
  -- TODO: handle corruptions

  -- _2pid :: Map (String) (p2a,a2p,z2p,...)
  z2pid <- newIORef empty
  f2pid <- newIORef empty
  a2pid <- newIORef empty

  -- subroutine to install a new party
  let newPid pid = do
        liftIO $ putStrLn $ "Creating new party with pid:" ++ pid
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
        a <- newPid' a2pid p2a "p2a"
        fork $ p pid z f a
        return ()

  let getPid _2pid pid = do
        b <- return . member pid =<< readIORef _2pid
        if not b then newPid pid else return ()
        readIORef _2pid >>= return . (! pid)

  fork $ forever $ do
    (pid, m) <- readChan z2p
    liftIO $ putStrLn $ "party wrapper z->p received"
    getPid z2pid pid >>= flip writeChan m

  fork $ forever $ do
    (pid, m) <- readChan f2p
    liftIO $ putStrLn $ "party wrapper f->p received"
    getPid f2pid pid >>= flip writeChan m

  fork $ forever $ do
    (pid, m) <- readChan a2p
    liftIO $ putStrLn $ "party wrapper a->p received"
    getPid a2pid pid >>= flip writeChan m

  return ()


idealProtocol pid (z2p, p2z) (f2p, p2f) (a2p, p2a) = do
  fork $ forever $ do
    m <- readChan z2p
    liftIO $ putStrLn $ "idealProtocol received from z2p " ++ pid
    writeChan p2f m
  fork $ forever $ do
    m <- readChan f2p
    liftIO $ putStrLn $ "idealProtocol received from f2p " ++ pid
    writeChan p2z m
  fork $ forever $ do
    m <- readChan a2p
    liftIO $ putStrLn $ "idealProtocol received from a2p " ++ pid
    fail "adv"
    writeChan p2a m
  return ()

dummyAdversary (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >>= writeChan a2f
  fork $ forever $ readChan f2a >>= writeChan a2z
  return ()

dummyFunctionality (p2f, f2p) (a2f, f2a) = do

  fork $ forever $ do
    (pid, m :: Int) <- readChan p2f 
    liftIO $ putStrLn $ "F: [" ++ pid ++ "] " ++ show m
    writeChan f2p $ (pid, ())
  fork $ forever $ do
    () <- readChan a2f
    liftIO $ putStrLn $ "F: A"
    writeChan f2a $ ()

  return ()
              
testEnv (p2z, z2p) (a2z, z2a) pump outp = do
  fork $ forever $ do
    x :: (String, ()) <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    --writeChan outp ()
    pass

  fork $ forever $ do
    x <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent "
    writeChan outp ()

  () <- readChan pump
  liftIO $ putStrLn "pump"
  b <- getBit
  if b then
      writeChan z2p ("Alice", 0)
  else
      writeChan z2p ("Bob", 1)

  () <- readChan pump
  writeChan z2a ()

testExec :: IO ()
testExec = runRand $ execUC testEnv (partyWrapper idealProtocol) dummyFunctionality dummyAdversary
