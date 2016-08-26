 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, AllowAmbiguousTypes
  #-} 

module AuthMap where

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

class HasFork m => MonadLeak a m | m -> a where
    leak :: a -> m ()

instance (HasFork m, MonadReader (Chan (SID, a), Chan ()) m) => MonadLeak a m where
    leak a = do
      --sid <- getSID
      (ci, co) <- ask
      writeChan ci (("",""), a)
      () <- readChan co
      return ()

runLeak f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  buffer <- newIORef []
  ci <- newChan
  co <- newChan

  f2a' <- wrapWrite LeakF2A_Through f2a
  a2f' <- newChan

  fork $ forever $ do
    (sid, a) <- readChan ci
    liftIO $ putStrLn $ "[fLeak]: " ++ show sid
    modifyIORef buffer (++ [(sid,a)])
    writeChan co ()

  fork $ forever $ do
    mf <- readChan a2f
    case mf of
      LeakA2F_Get -> do
                     buf <- readIORef buffer
                     writeChan f2a (LeakF2A_Leaks buf)
      LeakA2F_Through a -> writeChan a2f' a

  runReaderT (f crupt (p2f, f2p) (a2f', f2a') (z2f, f2z)) (ci,co)


{-- MonadOptionally --}
{-- This is a functionality typeclass that provides delayed and *unreliable* scheduling of a task. The adversary can choose to deliver the task at any time. --}
class HasFork m => MonadOptionally m where
    optionally :: m () -> m ()

instance (MonadReader (Chan (Chan ())) m, HasFork m, MonadIO m) => MonadOptionally m where
    optionally m = do
      ch :: Chan () <- newChan
      reg :: Chan (Chan ()) <- ask
      writeChan reg ch
      fork $ readChan reg >> m
      return ()

data OptionalA2F a = OptionalA2F_Deliver Int | OptionalA2F_Through a

runOptionally f crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  a2f' <- newChan
  reg <- newChan
  queue <- newIORef []
  fork $ forever $ do
    c <- readChan reg
    modifyIORef queue (++ [c])

  fork $ forever $ do
    mf <- readChan a2f
    case mf of
      OptionalA2F_Deliver i -> undefined
      OptionalA2F_Through m -> writeChan a2f' m

  runReaderT (f crupt (p2f, f2p) (a2f', f2a) (z2f, f2z)) reg


data AuthMapP2F a = AuthMapP2F_Init [a] | AuthMapP2F_Query Int
data AuthMapF2P a = AuthMapF2P_OK | AuthMapF2P_Resp (Int, a)

fAuthMap crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  fork $ do
    AuthMapP2F_Init xs <- readChan p2f
    writeChan f2p AuthMapF2P_OK
    forever $ do
           AuthMapP2F_Query i <- readChan p2f
           optionally $ do
                writeChan f2p $ AuthMapF2P_Resp (i, xs !! i)
           writeChan f2p AuthMapF2P_OK
