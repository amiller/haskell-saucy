{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds, PartialTypeSignatures
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
import Data.Map

import OptionallyLeak

data Void

data AuthMapP2F a = AuthMapP2F_Init [a] | AuthMapP2F_Query Int deriving Show
data AuthMapF2P a = AuthMapF2P_OK | AuthMapF2P_Resp (Int, a) deriving Show

fAuthMap (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  fork $ do
    -- First the mapping must be initialized, with an array
    mp <- readChan p2f
    let (pid, AuthMapP2F_Init xs) = mp

    -- No privacy is claimed in this protocol, so the entire contents are leaked
    leak xs
    writeChan f2p (pid, AuthMapF2P_OK)

    -- Next respond to queries
    forever $ do
           mp <- readChan p2f
           let (pid, AuthMapP2F_Query i) = mp
           -- Responses are optional, but if any answer is provided,
           -- it is guaranteed to be correct
           optionally $ do
                writeChan f2p $ (pid, AuthMapF2P_Resp (i, xs !! i))
           writeChan f2p $ (pid, AuthMapF2P_OK)
  return ()


--testEnvMapBenign :: MonadEnvironment m =>  Environment _ _ _ (SttCruptZ2A (AuthMapP2F Char) (OptionalA2F (LeakA2F a2f0))) Void Void () m
testEnvMapBenign z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestEnvMapBenign", "")
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    liftIO $ putStrLn $ "Z: Party[" ++ pid ++ "] output " ++ show m
    ?pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " -- ++ show m
    ?pass

  -- Have Alice configure the initial dictionary
  () <- readChan pump
  writeChan z2p ("Alice", AuthMapP2F_Init "hello")

  -- Have Bob request twice
  () <- readChan pump
  writeChan z2p ("Bob", AuthMapP2F_Query 1)
  () <- readChan pump
  writeChan z2p ("Bob", AuthMapP2F_Query 2)

  -- Let the adversary read the buffer
  () <- readChan pump 
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Through LeakA2F_Get

  -- Let the adversary deliver the respones out of order
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 1
  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F $ OptionalA2F_Deliver 0

  () <- readChan pump 
  writeChan outp () --"environment output: 1"


test :: IO ()
test = runITMinIO 120 $ execUC testEnvMapBenign idealProtocol (runOptLeak fAuthMap) dummyAdversary
