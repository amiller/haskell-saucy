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

import OptionallyLeak


data AuthMapP2F a = AuthMapP2F_Init [a] | AuthMapP2F_Query Int
data AuthMapF2P a = AuthMapF2P_OK | AuthMapF2P_Resp (Int, a)

fAuthMap optionally crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  fork $ do
    AuthMapP2F_Init xs <- readChan p2f
    leak xs
    writeChan f2p AuthMapF2P_OK
    forever $ do
           AuthMapP2F_Query i <- readChan p2f
           optionally $ do
                writeChan f2p $ AuthMapF2P_Resp (i, xs !! i)
           writeChan f2p AuthMapF2P_OK
