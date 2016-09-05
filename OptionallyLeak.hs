 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, AllowAmbiguousTypes
  #-} 

module OptionallyLeak where

import ProcessIO
import StaticCorruptions
import Safe

import Control.Concurrent.MonadIO
import Control.Monad (forever)
import Control.Monad.State (lift)
import Control.Monad.Reader

import Data.IORef.MonadIO

{-- MonadLeak --}
data LeakA2F a   = LeakA2F_Get              | LeakA2F_Through a deriving Show
data LeakF2A a b = LeakF2A_Leaks [(SID, a)] | LeakF2A_Through b deriving Show

runLeak f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  sid <- getSID

  buffer <- newIORef []

  f2a' <- wrapWrite LeakF2A_Through f2a
  a2f' <- newChan

  let leak x = do
        modifyIORef buffer (++ [(sid,x)])
        return ()

  fork $ forever $ do
    mf <- readChan a2f
    case mf of
      LeakA2F_Get -> do
                     buf <- readIORef buffer
                     writeChan f2a (LeakF2A_Leaks buf)
      LeakA2F_Through a -> writeChan a2f' a

  f leak crupt (p2f, f2p) (a2f', f2a') (z2f, f2z)


{-- MonadOptionally --}
{-- This is a functionality typeclass that provides delayed and *unreliable* scheduling of a task. The adversary can choose to deliver the task at any time. --}
{--
--class HasFork m => MonadOptionally m where
--    optionally :: m () -> m ()

instance (MonadReader (Chan (Chan ())) m, HasFork m, MonadIO m) => MonadOptionally m where
    optionally m = do
      ch :: Chan () <- newChan
      reg :: Chan (Chan ()) <- ask
      writeChan reg ch
      fork $ readChan reg >> m
      return ()

--}

data OptionalA2F a = OptionalA2F_Deliver Int | OptionalA2F_Through a

deleteNth i xs = l ++ r where (l,(_:r)) = splitAt i xs

runOptionally f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Build the "optionally" function
  queue <- newIORef []
  let optionally m = do
        c :: Chan () <- newChan
        modifyIORef queue (++ [c])
        fork $ readChan c >> m
        return ()

  a2f' <- newChan

  fork $ forever $ do
    mf <- readChan a2f
    case mf of
      OptionalA2F_Deliver i -> do
                     q <- readIORef queue
                     modifyIORef queue (deleteNth i)
                     writeChan (q !! i) ()
      OptionalA2F_Through m -> writeChan a2f' m

  f optionally crupt (p2f, f2p) (a2f', f2a) (z2f, f2z)

runOptLeak f = runOptionally f'' where
    f'' optionally = runLeak f' where
        f' leak = f leak optionally
