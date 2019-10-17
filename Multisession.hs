 {-# LANGUAGE ImplicitParams, Rank2Types, ScopedTypeVariables
  #-} 

{- 

 -}


module Multisession where

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)
import Control.Monad.Reader

import System.Random

import ProcessIO
import StaticCorruptions

import Data.IORef.MonadIO
import Data.Map.Strict
import Safe

data Void
instance Show Void where
  show = undefined



{- Multi-session extensions -}

{-
 Given a functionality F, the multisession extension, !F, 
 allows access to an arbitrary number of subinstances of F.
 Each subinstance of F is passed a distinct SID string.
 A composition theorem states that given a protocol pi realizing F,
 !pi realizes !F (for the obvious natural definition of multisession 
 protocols !pi)

 -}

bangF
  :: MonadFunctionality m =>
     (forall m'. MonadFunctionality m' => Functionality p2f f2p a2f f2a z2f f2z m') ->
     Functionality (SID, p2f) (SID, f2p) (SID, a2f) (SID, f2a) (SID, z2f) (SID, f2z) m
bangF f (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Store a table that maps each SSID to a channel (f2p,a2p) used
  -- to communicate with each subinstance of !f
  p2ssid <- newIORef empty
  a2ssid <- newIORef empty
  z2ssid <- newIORef empty

  let newSsid ssid = do
        liftIO $ putStrLn $ "[" ++ show ?sid ++ "] Creating new subinstance with ssid: " ++ show ssid
        let newSsid' _2ssid f2_ tag = do
                     ff2_ <- newChan;
                     _2ff <- newChan;
                     fork $ forever $ do
                                  m <- readChan ff2_
                                  --liftIO $ putStrLn $ "!F wrapper f->_ received " ++ tag -- ++ " " ++ show m
                                  writeChan f2_ (ssid, m)
                     modifyIORef _2ssid $ insert ssid _2ff
                     return (_2ff, ff2_)
        f2p' <- wrapWrite (\(_, (pid, m)) -> (pid, (ssid, m))) f2p
        p <- newSsid' p2ssid f2p' "f2p"
        a <- newSsid' a2ssid f2a "f2a"
        z <- newSsid' z2ssid f2z "f2z"
        fork $ let ?sid = (extendSID ?sid (fst ssid) (snd ssid)) in do
          liftIO $ putStrLn $ "in forked instance: " ++ show ?sid
          f p a z
        return ()

  let getSsid _2ssid ssid = do
        b <- return . member ssid =<< readIORef _2ssid
        if not b then newSsid ssid else return ()
        readIORef _2ssid >>= return . (! ssid)

  -- Route messages from parties to functionality
  fork $ forever $ do
    (pid, (ssid, m)) <- readChan p2f
    --liftIO $ putStrLn $ "!F wrapper p->f received " ++ show ssid
    getSsid p2ssid ssid >>= flip writeChan (pid, m)

  -- Route messages from adversary to functionality
  fork $ forever $ do
    (ssid, m) <- readChan a2f
    --liftIO $ putStrLn $ "!F wrapper a->f received " ++ show ssid
    getSsid a2ssid ssid >>= flip writeChan m
  return ()


--
bangP p (z2p, p2z) (f2p, p2f) = do
  -- Store a table that maps each SSID to a channel (z2p,f2p) used
  -- to communicate with each subinstance of !p
  z2ssid <- newIORef empty
  f2ssid <- newIORef empty

  let newSsid ssid = do
        liftIO $ putStrLn $ "[" ++ show ?sid ++ "] Creating new protocol subinstance with ssid: " ++ show ssid
        let newSsid' _2ssid p2_ tag = do
                     pp2_ <- newChan;
                     _2pp <- newChan;
                     fork $ forever $ do
                                  m <- readChan pp2_
                                  liftIO $ putStrLn $ "!P wrapper p->_ received " ++ tag
                                  writeChan p2_ (ssid, m)
                     modifyIORef _2ssid $ insert ssid _2pp
                     return (_2pp, pp2_)
        z <- newSsid' z2ssid p2z "p2z"
        f <- newSsid' f2ssid p2f "p2f"
        fork $ let ?sid = (extendSID ?sid (fst ssid) (snd ssid)) in
          p z f
        return ()

  let getSsid _2ssid ssid = do
        b <- return . member ssid =<< readIORef _2ssid
        if not b then newSsid ssid else return ()
        readIORef _2ssid >>= return . (! ssid)

  -- Route messages from environment to parties
  fork $ forever $ do
    (ssid, m) <- readChan z2p
    liftIO $ putStrLn $ "!P wrapper z->p received " ++ show ssid
    getSsid z2ssid ssid >>= flip writeChan m

  -- Route messages from functionality to parties
  fork $ forever $ do
    (ssid, m) <- readChan f2p
    liftIO $ putStrLn $ "!P wrapper f->p received " ++ show ssid
    getSsid f2ssid ssid >>= flip writeChan m
  return ()


-- Theorem statement:
--    (pi,f) ~ (phi,g) --> (!pi,!f) ~ (!phi,!g)
--
-- squashS below is a simulator for this statement


{- Test cases for multisession -}

testEnvMulti z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("sid1","") empty

  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    --writeChan outp "()"
    ?pass

  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m
    writeChan outp "environment output: 1"

  () <- readChan pump
  liftIO $ putStrLn "pump"
  b <- ?getBit
  if b then
      writeChan z2p ("Alice", (("ssidX",""), show "0"))
  else
      writeChan z2p ("Bob", (("ssidX",""), show "1"))

  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F (("ssidX",""), "ok")


testExecMulti :: IO String
testExecMulti = runITMinIO 120 $ execUC testEnvMulti (bangP idealProtocol) (bangF dummyFunctionality) dummyAdversary


{- Squash Theorem -}
{- !F -> !!F -}
{- (squash,!F) ~ (idealP,!!F) -}

squash (z2p, p2z) (f2p, p2f) = do
  fork $ forever $ do
    (ssid :: SID, (sssid :: SID, m)) <- readChan z2p
    writeChan p2f ((show (ssid, fst sssid), snd sssid), m)
  fork $ forever $ do
    (s :: SID, m) <- readChan f2p
    --liftIO $ putStrLn $ "squash [f2p]: " ++ show s
    let sndsssid = snd s
    let (ssid :: SID, fstsssid) :: (SID, String) = readNote "squash" $ fst s
    let sssid = (fstsssid, sndsssid)
    writeChan p2z (ssid, (sssid, m))
  return ()

testEnvSquash z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("sid1","") empty

  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    --writeChan outp "()"
    ?pass

  fork $ forever $ do
    m <- readChan a2z -- :: SttCruptA2Z (SID, String) (SID, a) <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show m
    writeChan outp "environment output: 1"

  () <- readChan pump
  liftIO $ putStrLn "pump"
  b <- ?getBit
  if b then
      writeChan z2p ("Alice", (("ssidY",""), (("sssidX",""), "0")))
  else
      writeChan z2p ("Bob",   (("ssidY",""), (("sssidX",""), "1")))

  () <- readChan pump
  writeChan z2a $ SttCruptZ2A_A2F ((show (("ssidY",""), "sssidX"), ""), "ok")


squashS (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ do
    mf <- readChan z2a
    case mf of
      SttCruptZ2A_A2P (pid, (s, m)) -> do
                     let sndsssid = snd s
                     let (ssid :: SID, fstsssid) :: (SID, String) = readNote "squashS" $ fst s
                     let sssid = (fstsssid, sndsssid)
                     writeChan a2p (pid, (ssid, (sssid, m)))
      SttCruptZ2A_A2F (s, m)        -> do
                     let sndsssid = snd s
                     let (ssid :: SID, fstsssid) :: (SID, String) = readNote "squashS" $ fst s
                     let sssid = (fstsssid, sndsssid)
                     writeChan a2f $ (ssid, (sssid, m))

  fork $ forever $ do
    (pid, (ssid, (sssid, m))) <- readChan p2a
    writeChan a2z $ SttCruptA2Z_P2A (pid, ((show (ssid, fst sssid), snd sssid), m))
    fail "unknown!"

  fork $ forever $ do
    (ssid, (sssid, m)) <- readChan f2a
    writeChan a2z $ SttCruptA2Z_F2A ((show (ssid, fst sssid), snd sssid), m)

  return ()


testExecSquashReal :: IO String
testExecSquashReal = runITMinIO 120 $ execUC testEnvSquash squash (bangF dummyFunctionality) dummyAdversary

testExecSquashIdeal :: IO String
testExecSquashIdeal = runITMinIO 120 $ execUC testEnvSquash ((idealProtocol)) (bangF (bangF dummyFunctionality)) squashS


{-- Remark: applying (bangP idealProtocol) is equiv to just (idealProtocol),
            so all of these variations are equivalent--}
testExecSquashIdeal' :: IO String
testExecSquashIdeal' = runITMinIO 120 $ execUC testEnvSquash (bangP (idealProtocol)) (bangF (bangF dummyFunctionality)) squashS

testExecSquashIdeal'' :: IO String 
testExecSquashIdeal'' = runITMinIO 120 $ execUC testEnvSquash (bangP (bangP idealProtocol)) (bangF (bangF dummyFunctionality)) squashS
