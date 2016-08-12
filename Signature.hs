 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses
  
  #-} 

{-
  Here we advocate a new UC model for public-key signatures.

  In general, when designing functionalities based on existing protocols, we should should abstract away from implementation details of the protocols being modeled.

  When applying this guideline to signature schemes, we encounter the following dilemma: should the functionality expose concrete "signature" strings? If so, how are signature strings chosen?

  Avoiding signature strings seems not to work. The most natural idea is to have the functionality keep track of which messages have been signed, and allow anyone to query whether a message m has been signed by party P. However, this would be too strong - it doesn't model the fact that the signature string must be transmitted to a verifier before such a query can succeed. It also is infeasible to write a functionality that keeps track of which parties are and aren't allowed to make each query, since signatures can ultimately be transmitted out of band.

  Another unworkable approach is to have the functionality generate from a fixed (e.g., uniform) distribution.

  The subsequent models [Can01,Can05, others] all feature some form of adversarially-chosen signatures. The functionality passes around these adversarially-chosen strings, except it checks whether the responses satisfy the security requirements; any case where the functionality violates the properties is a  "bad event". The different approaches vary in how they respond to a bad event.

  Our approach is to "suppress" the bad events, as in [Can01]. This approach has the following two virtues:

  - A protocol that embeds a correct signature scheme must never cause one of these bad events to occur, since an adversary that causes a bad event to occur would not be simulatable in the ideal world with the overpowered default.

  - A protocol that *depends* on this functionality to realize some other primitive F cannot rely on any special properties of the ``overpowered'' default, since it must satisfy F regardless of the adversary's choice.

  Other related approaches also feature "Bad events" in functionalities:
  - In Can05, Hofheinz, Cl05, a bad event immediately informs the environment.
    This is in fact the opposite direction.
    It makes it so that even in the ideal world, things can go very bad (this weakens the definition). We prefer to make the ideal world even better.

\footnote{
  A related approach is rational protocol design: here "bad events" may occur, but metatheory logic can refer to these and argue they do not happen (e.g., in a nash equilibrium with a rational adversary, the bad events do not occur).
}

  A second way our approaches differ is in *how* the signature strings are obtained from the adversary. In [Can01], the adversary adaptively chooses each new signature string upon each "sign" query from an honest party. One objection to this is that this conveys too much information to the adversary (after all, signing can be done locally without involving the network); another objection is that the adversary can technically halt execution by refusing to return any string. In later versions, the adversary is notified just the first time a party generates a key; the adversary then chooses the signing functions which are used thereafter. This addresses the first objection but not the latter.

  In our variation of the model, we simply allow a concrete signing scheme to be a parameter of the fuctionality. Correspondingly, our composition theorem only applies to hybrid-protocols that do not make use of any specific properties of the signature scheme other than those enforced by the functionality. This is expressed directly using quantification.

  Our composition theorem can thus be stated in concise notation as follows:

    (runSignature scheme, fA) =realizes= (fSig scheme)
    forall scheme: (pi, (fSig scheme)) =realizes= fB
    ------------
    (compose pi (runSignature scheme), fA) =realizes= fB


  To recap, a summary of adversarial choices in F_sig models:
  - [Can01] Adversary is notified every time a message is signed by an honest party, and chooses the concrete signature string. Bad events are suppressed.

  - [Hofheinz] Adversary is notified ???. Bad events are catastrophic.

  - [CL06, and others] Adversary is notified the first time an honest party generates a key, and chooses a concrete protocol. Bad events are catastrophic.

  - Ours:
      Adversary is *not* notified as a result of any signing operations. We simply require that a quantifier is added over all algorithms.
      Bad events are suppressed.



  Things this model captures:
  - PKI:
     Keygen is implicitly

  - Unforgeability:
     If the signer is honest, then an attacker cannot create a valid signature on m unless m has previousy been signed.

  - Signature malleability:
     Even if the signer is honest, the adversary can create new valid signatures for previously signed messages

  - Correctness:
     A signing query is guaranteed to return a verifying signature

  - Non-verifiable keygen:
     If the signer is corrupted, no guarantees are made

  - No hidden information:
     The signing algorithm is stateless, so it does not reveal any information about which messages have been signed or not

  - [CL2006] On Signatures of Knowledge http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.75.1454&rep=rep1&type=pdf
    Appendix B explains the story of signatures.
  - Hofheinz ????? TODO
 -}


-- Signatures
module Signature where


import ProcessIO
import StaticCorruptions

import Control.Concurrent.MonadIO
import Control.Monad (forever)
import Control.Monad.State
import Control.Monad.Reader
import Safe

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map
import Control.Monad.Except

type SignaturePK = String
type SignatureSK = String
type SignatureSig = String

data SignatureP2F a = SignatureP2F_Sign a |
                      SignatureP2F_Verify a SignatureSig deriving Show
data SignatureF2P = SignatureF2P_OK | 
                    SignatureF2P_Sig SignatureSig |
                    SignatureF2P_Verify Bool deriving Show
                                                                        
--data SignatureF2A a = SignatureF2A a deriving Show
--data SignatureA2F a = SignatureA2F_Deliver PID deriving Show

defaultSignature :: HasFork m => 
     (m (SignatureSK, SignaturePK),
      SignatureSK -> String -> m SignatureSig,
      SignaturePK -> String -> SignatureSig -> Bool)
defaultSignature = (gen, sign, verify) where
    gen = return ("SK", "PK")
    sign sk m = return "DEFAULTSIG"
      -- rnd :: Integer <- get32bytes
      -- return $ "DEFAULTSIG:" ++ show rnd
    verify pk m sig = True


fSignature :: (MonadSID m, HasFork m) =>
     (m (SignatureSK, SignaturePK),
      SignatureSK -> String -> m SignatureSig,
      SignaturePK -> String -> SignatureSig -> Bool)
     -> Crupt
     -> (Chan (PID, SignatureP2F String), Chan (PID, SignatureF2P))
     -> (Chan Void, Chan Void)
     -> (Chan Void, Chan Void)
     -> m ()

fSignature (keygen, sign, verify) crupt (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Functions are a parameter here

  -- Parse SID as signer
  sid <- getSID
  let (pidS :: PID, ssid :: String) = readNote "fSignature" $ snd sid

  -- Store state, including keypairs and signed messages
  keypairs <- newIORef (empty :: Map PID (SignatureSK,SignaturePK))
  records  <- newIORef (empty :: Map String ())

  let getKeys pid = do
        kps <- readIORef keypairs
        if (not $ member pid kps) then do
              (sk, pk) <- keygen
              writeIORef keypairs (Map.insert pid (sk, pk) kps)
              return (sk, pk)
        else
            let Just (sk, pk) = Map.lookup pid kps in
            return (sk, pk)

  fork $ forever $ do
    (pid, mf) <- readChan p2f
    case mf of
        SignatureP2F_Sign m -> do
          -- Only designated signer can sign
          assert (pid == pidS) "Sign called by wrong party"

          (sk,pk) <- getKeys pidS

          -- Create a new signature using the provided algorithm
          sig <- sign sk m
          -- If the signature does not verify, then throw an error
          if not (verify pk m sig) then
              fail "[fSig] Correctness Error"
              --throwError "[fSig] Correctness Error"
          else return ()

          -- Add signature record
          modifyIORef records (Map.insert m ())
          writeChan f2p (pid, SignatureF2P_Sig sig)

        SignatureP2F_Verify m sig -> do
          (_, pk) <- getKeys pidS

          -- If the signer is corrupted, just evaluate verify
          if member pidS crupt then
              writeChan f2p (pid, SignatureF2P_Verify (verify pk m sig))
          else do
              -- Check whether the signature has been recorded
              recs <- readIORef records
              if (verify pk m sig) && (not $ Map.member m recs) then
                  fail "[fSig] Unforgeability Error"
                  --throwError "[fSig] Unforgeability Error"
              else return ()

              writeChan f2p (pid, SignatureF2P_Verify (verify pk m sig))

  return ()

         
testEnvSig z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestSig", show ("Alice",""))
  writeChan z2exec $ SttCrupt_SidCrupt sid empty
  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " ++ show x
    pass
  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " ++ show (m :: SttCruptA2Z (SignatureF2P) Void)
    pass
  fork $ forever $ do
    f <- readChan f2z
    liftIO $ putStrLn $ "Z: f sent " ++ show (f :: Void)
    pass

  -- Have Alice sign a message
  () <- readChan pump 
  writeChan z2p ("Alice", SignatureP2F_Sign "hi Bob")

  -- Have Bob check the message
  () <- readChan pump 
  writeChan z2p ("Bob", SignatureP2F_Verify "hi Bob" "")

  () <- readChan pump 
  writeChan outp "environment output: 1"
            

voidSigScheme :: Monad m => (m (SignatureSK, SignaturePK), 
                             SignatureSK -> String -> m SignatureSig,
                             SignaturePK -> String -> SignatureSig -> Bool)
voidSigScheme = (return ("SK","PK"), \sk m-> return "SIG", \pk m sig-> True)

testSig :: IO String
testSig = runRand $ execUC testEnvSig (idealProtocol) (fSignature voidSigScheme) (dummyAdversary)
