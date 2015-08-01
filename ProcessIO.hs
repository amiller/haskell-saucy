{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  RankNTypes, OverlappingInstances
  #-} 

{- It's possible to use Haskell's ugly IO channels as a way of implementing message passing. 

   Typing is very lose.
   It does not guarantee that:
   - there is only one active reader for each channel
   - a read is followed by at most one write
   - channels are not passed over channels
   - closures are not passed over channels

   But we can still use this technique as a way of implementing these.

   Finally-Tagless-Pi is a way of implementing a Pi-like language using this technique.
   https://mail.haskell.org/pipermail/haskell-cafe/2010-June/078780.html

 -}

{-
   import Control.Concurrent.Chan.Synchronous
-}
module ProcessIO where

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)
import Control.Monad.Reader

import System.Random

assert cond msg = if not cond then fail msg else return ()

{- Syntax sugar for parallel composition -}
(|||) :: HasFork m => m () -> m () -> m ()
p ||| q = fork p >> q
infixl 1 |||

multiplex :: HasFork m => Chan a -> Chan b -> m (Chan (Either a b))
multiplex a b = do
  c <- newChan
  fork $ forever $ readChan a >>= writeChan c . Left
  fork $ forever $ readChan b >>= writeChan c . Right
  return c

demultiplex :: HasFork m => Chan (Either a b) -> Chan a -> Chan b -> m ()
demultiplex ab a b = forever $ do
                       x <- readChan ab
                       case x of
                         Left  y -> writeChan a y
                         Right y -> writeChan b y
                                                    
{- Several monad typeclasses are useful for composing processes.
   These classes effectively just involve keeping track of special channels.
   They are implemented using the ReaderT monad transformer.  -}

-- We need the following instance showing that fork works with ReaderT
instance HasFork m => HasFork (ReaderT s m) where
    fork p = do
      s <- ask
      lift $ fork $ runReaderT p s


{- Randomized Algorithms -}
{- Processes can request random bits. Under the hood, these are implemented as ordinary channels -}
class HasFork m => MonadRand m where
    getBit :: m Bool

type RandomMonadT m = ReaderT (Chan (), Chan Bool) m
    
instance HasFork m => MonadRand (RandomMonadT m) where
    getBit = do 
      (ri,ro) <- ask
      writeChan ri ()
      readChan ro

instance MonadRand m => MonadRand (ReaderT s m) where
    getBit = lift getBit

runRand :: HasFork m => RandomMonadT m a -> m a
runRand p = do
  ri <- newChan
  ro <- newChan
  fork $ forever $ readChan ro >>= (const $ liftIO $ randomRIO (False,True)) >>= writeChan ri
  runReaderT p (ro, ri)

_flippedRand :: MonadRand m => (forall n. MonadRand n => n a) -> m a
_flippedRand f = do
  ri <- newChan
  ro <- newChan
  fork $ forever $ do
                   () <- readChan ri
                   b <- getBit
                   liftIO $ putStrLn $ "inner flip: " ++ show b
                   writeChan ro (not b)
  runReaderT f (ri, ro)

test2 :: MonadRand m => m Bool
--test2 = runRand getBit
test2 = runRand $ _flippedRand getBit


{- Provides a default channel to send on, when no message is intended -}
class HasFork m => MonadDefault m where
    pass :: m ()

instance (HasFork m) => MonadDefault (ReaderT (Chan ()) m) where
    pass = ask >>= flip writeChan ()

instance MonadDefault m => MonadDefault (ReaderT s m) where
    pass = lift pass
      
runDefault :: HasFork m => Chan () -> ReaderT (Chan ()) m a -> m a
runDefault = flip runReaderT


{- Simple examples -}
doubler :: Num a => Chan a -> Chan a -> IO ()
doubler i o = do
  x <- readChan i
  writeChan o (x*2)

flipWrite a b = do
  x <- getBit
  if x then writeChan a ()
  else      writeChan b ()

counter a b = do
  ab <- multiplex a b
  let counter' n = do
                c <- readChan ab
                case c of 
                  Left  s -> liftIO $ putStrLn ("a" ++ show n)
                  Right s -> liftIO $ putStrLn ("b" ++ show n)
                counter' (n+1)
  counter' 0

-- Ask for a random bit, and print a message according to which one
test1 :: MonadRand m => m ()
test1 = do
  a <- newChan
  b <- newChan
  fork $ counter a b
  replicateM_ 10 $ flipWrite a b

--test1run :: IO ()
--test1run = do { runRand $ test1; threadDelay 1000}


