{-# LANGUAGE Rank2Types, ImplicitParams
  #-} 

{- It's possible to use Haskell's channels as a way of implementing message passing. 

   However, the type restrictions here are looser than in ILC.
   Control.Concurrent does not guarantee that:
   - there is only one active reader for each channel
   - a read is followed by at most one write
   - channels are not passed over channels

   But we can still use this technique as a way of implementing these.

 -}

{-
   import Control.Concurrent.Chan.Synchronous
-}
module ProcessIO where

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)

import System.Random

data Void 
instance Show Void where
    show = undefined

{-- Simple utilities for working with channels --}
wrapWrite f c = do
  d <- newChan 
  fork $ forever $ readChan d >>= writeChan c . f 
  return d

wrapRead f c = do
  d <- newChan
  fork $ forever $ readChan c >>= writeChan d . f 
  return d

assert cond msg = if not cond then fail msg else return ()

{- Syntax sugar for parallel composition, returning the right value -}
(|.) :: HasFork m => m () -> m () -> m ()
p |. q = fork p >> q
infixl 1 |.

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


{- Randomized Algorithms -}
{- Processes can request random bits. Under the hood, these are implemented as ordinary channels -}

runRand :: HasFork m => ((?getBit :: m Bool) => m a) -> m a
runRand p = let ?getBit = (liftIO $ randomRIO (False,True)) in p

--getNbits :: (Num a, Monad m, ?getBit :: m Bool) => Int -> m a
getNbits 0 = return 0
getNbits n | n < 0 = fail "negative bits?"
getNbits n = do
  b <- ?getBit
  rest <- getNbits (n-1)
  return $ 2*rest + if b then 0 else 1

get32bytes :: (Num a, Monad m, ?getBit :: m Bool) => m a
get32bytes = getNbits (32*8)

--flippedRand :: (HasFork m, ?getBit :: m Bool) => ((?getBit :: m Bool) => m a) -> m a
flippedRand f = let ?getBit = ?getBit >>= (return . not) in f

test2 :: IO Bool
--test2 = runRand ?getBit
test2 = runRand $ flippedRand ?getBit


{- Provides a default channel to send on, when no message is intended -}

runDefault :: HasFork m => Chan () -> ((?pass :: m ()) => m a) -> m a
runDefault c f = let ?pass = writeChan c () in f


{- Simple examples -}
doubler :: Num a => Chan a -> Chan a -> IO ()
doubler i o = do
  x <- readChan i
  writeChan o (x*2)

flipWrite a b = do
  x <- ?getBit
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
test1 :: (HasFork m, ?getBit :: m Bool) => m ()
test1 = do
  a <- newChan
  b <- newChan
  fork $ counter a b
  replicateM_ 10 $ flipWrite a b

test1run :: IO ()
test1run = do { runRand $ test1; threadDelay 1000}
