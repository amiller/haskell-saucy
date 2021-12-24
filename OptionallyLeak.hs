{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds
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
type MonadLeak m l = (MonadFunctionality m,
                    ?leak :: l -> m ())

leak :: MonadLeak m l => l -> m ()
leak = ?leak

data LeakA2F a   = LeakA2F_Get              | LeakA2F_Through a deriving Show
data LeakF2A a b = LeakF2A_Leaks [(SID, a)] | LeakF2A_Through b deriving Show

runLeak :: MonadFunctionality m =>
   (MonadLeak m l => Functionality p2f f2p a2f f2a z2f f2z m) ->
                     Functionality p2f f2p (LeakA2F a2f) (LeakF2A l f2a) z2f f2z m
runLeak f (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  buffer <- newIORef []

  f2a' <- wrapWrite LeakF2A_Through f2a
  a2f' <- newChan

  let leak x = do
        modifyIORef buffer (++ [(?sid,x)])
        return ()

  fork $ forever $ do
    mf <- readChan a2f
    case mf of
      LeakA2F_Get -> do
                     buf <- readIORef buffer
                     writeChan f2a (LeakF2A_Leaks buf)
      LeakA2F_Through a -> writeChan a2f' a

  let ?leak = leak in
    f (p2f, f2p) (a2f', f2a') (z2f, f2z)



{-- MonadOptionally --}
{-- This is a functionality typeclass that provides delayed and *unreliable* scheduling of a task. The adversary can choose to deliver the task at any time. --}

type MonadOptionally m = (MonadFunctionality m,
                          ?optionally :: m () -> m ())

optionally :: MonadOptionally m => m () -> m ()
optionally = ?optionally


data OptionalA2F a = OptionalA2F_Deliver Int | OptionalA2F_Through a

deleteNth i xs = l ++ r where (l,(_:r)) = splitAt i xs

runOptionally :: MonadFunctionality m =>
   (MonadOptionally m => Functionality p2f f2p a2f f2a z2f f2z m) ->
                         Functionality p2f f2p (OptionalA2F a2f) f2a z2f f2z m
runOptionally f (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Implement the `optionally` keyword. Optionally is backed by a task queue.
  -- Invoking `optionally m` schedules code block `m` for later execution.
  -- The tasks in the queue can be executed in any order, or not at all, as
  -- determined by the adversary.
  queue <- newIORef []
  let optionally m = do
        c :: Chan () <- newChan
        modifyIORef queue (++ [c])
        fork $ readChan c >> m
        return ()

  -- Adversary chooses which message to deliver based on their index in the queue.
  -- 
  a2f' <- newChan
  fork $ forever $ do
    mf <- readChan a2f
    case mf of
      OptionalA2F_Deliver i -> do
                     q <- readIORef queue
                     modifyIORef queue (deleteNth i)
                     writeChan (q !! i) ()
      OptionalA2F_Through m -> writeChan a2f' m

  let ?optionally = optionally in
   f (p2f, f2p) (a2f', f2a) (z2f, f2z)

runOptLeak :: MonadFunctionality m =>
  ((MonadOptionally m, MonadLeak m l) => Functionality p2f f2p a2f f2a z2f f2z m) ->
      Functionality p2f f2p (OptionalA2F (LeakA2F a2f)) (LeakF2A l f2a) z2f f2z m
runOptLeak f = runOptionally $ runLeak f
