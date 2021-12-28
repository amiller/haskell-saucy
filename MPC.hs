{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds, PartialTypeSignatures
  #-} 

module MPC where

import Control.Concurrent.MonadIO
import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map
import Control.Monad (forever,foldM)

import Data.Poly
import Data.Field.Galois (Prime, toP)
import Data.Vector (forM,fromList)

import ProcessIO
import StaticCorruptions
import OptionallyLeak (MonadOptionally, runOptionally, optionally)
import Polynomial
import Safe

data Void

type MonadMPC_F m = (MonadFunctionality m,
                     ?n :: Int,
                     ?t :: Int)

{--
 We model MPC as a service that keeps track of secret data.
 A sequence of operations are chosen by the adversary,
  but become common knowledge.
 Inputs are provided by a designated client.

 The operations available to the service are
  LIN, OPEN, RAND.

 - OPEN reveals the entire secret share.
 - LIN returns a linear combination of existing values

 We can show how to extend the functionality with more complex operations
 like
  MULT.
 --}

data FmpcOp sh = MULT sh sh sh | LIN sh Fq [(Fq,sh)] | INPUT sh Fq | RAND sh sh sh | OPEN sh

type Sh = Int
data FmpcP2F = FmpcP2F_Op (FmpcOp Sh) | FmpcP2F_Read Sh | FmpcP2F_MyShare Sh
data FmpcF2P = FmpcF2P_Ok | FmpcF2P_Open Fq | FmpcF2P_Share Fq


{----
 Interacting with the MPC Arithmetic BlackBox functionality

 It's essential in every MPC protocol that the honest parties agree on which sequence of operations to run.
 For maximum flexibility, we can allow these to be chosen by the adversary, but can read them.

 F_ArithmeticBlackBox.
   Keeps track of confidential data namespace.
   Carries out a specified arithmetic-circuit on the data within the confidential namespace.
   Discloses only the information specified by explicit "Open" commands.

 F_MPC
   In addition to an underlying confidential data stream, it keeps track of a secret share encoding of each secret value.
   Each party can read their polynomial share. Naturally, the adversary receives $t$ shares, but these reveal no information about $x$ (to summarize why F_MPC easily realizes ABB).

 F_MPC+
   The main construction we analyze is the Beaver Multiplication.
   This shows how to enrich the operation with multiplication. It's an intermediate step between F_MPC and F_ArithmeticBlackBox.


In a more realistic model, the sequence of operations would be chosen through a consensus process, like a smart contract. Allow us to provide Availability guarantees.

Defining F_MPC in more detail.
  The interface should be easily extensible, the way we add MULT should be a good example for how to add others.

 We know we want to write MPC pseudocode that looks like:
 BeaverMult: [x] [y]
   Preprocessing get [a][b][ab].
   D= open([x]-[a]) ...
   return [xy] := [ab]+D ...


The real challenge is that we want to be able to construct simulator proofs as well.
The simulator proof will need to intercept the Ids.
  See the real world, with additional variables present, such as the D and E in beaver multiplication. The environment expects to see these from the real world dummy adversary, but the functionality in the ideal world does not have any values for those. So if [x] and [y] correspond to registers $1 and $2, then [xy] in the ideal world would be $3, while in the real world.

Environment asks an honest party to query for one of the ephemeral values, it won't exist...
 ---}

--type MonadFMPC = MonadFMPC

mpcBeaver :: MonadMPCProtocol m sh => sh -> sh -> m sh
mpcBeaver x y = do
  (a,b,ab) <- getTriple
  d <- ?openShare =<< sub x a 
  e <- ?openShare =<< sub y b
  xy <- ?fresh
  de <- ?op CONST (d*e 
  ?op $ LIN xy [(1,ab),(d,a),(e,b)]
  return xy

sub :: MonadMPCProtocol m sh => sh -> sh -> m sh
sub x a = do
  x_a <- ?fresh
  ?op $ LIN x_a 1 [(1,x),(-1,a)]
  return x_a

getTriple :: MonadMPCProtocol m sh => m (sh,sh,sh)
getTriple = do
  a <- ?fresh; b <- ?fresh; ab <- ?fresh;
  ?op $ RAND a b ab
  return (a,b,ab)

type MonadMPCProtocol m sh = (Monad m,
                              ?op        :: FmpcOp sh -> m (),
                              ?openShare :: sh -> m Fq,
                              ?fresh     :: m sh)

runMPCprot :: MonadProtocol m =>
   (forall sh. MonadMPCProtocol m sh => m sh) -> m ()
runMPCprot m = do
   let ?op = undefined in
    let ?openShare = undefined in
     let ?fresh = undefined in
       m
   return ()

{--
  let ?open k:
    send OP to.
  let ?plus
--}

zero :: PolyFq
zero = polyFromCoeffs []

fMPC (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  memory <- newIORef (Map.empty :: Map Sh PolyFq)
  ops    <- newIORef []
  opened <- newIORef Map.empty

  -- Read operations from
  fork $ forever $ do
   (pid,m) <- readChan p2f
   case m of
     FmpcP2F_Op op -> do

     -- Append the op to the log
     modifyIORef ops $ (++) [op]

     -- Dispatch according to the op
     case op of
       MULT xy x y -> do
         if True then undefined else undefined
         return ()

       LIN k o cs -> do
         r <- foldM (\r -> \(c::Fq,x::Sh) ->  do
                     tbl <- readIORef memory
                     let Just xx = Map.lookup x tbl
                     return $ r + (toPoly $ fromList [c]) * xx) zero cs
         modifyIORef memory $ Map.insert k r
         return ()

       OPEN k -> do
         modifyIORef opened $ Map.insert k ()
          
       RAND ka kb kab -> do
         a <- randomDegree ?t
         b <- randomDegree ?t
         let aa :: Fq = eval a 0
         let bb :: Fq = eval b 0
         coeffs <- forM ([1..(?t-1)]::Vector Int) (\_ -> randFq)
         let ab = toPoly $ (fromList [aa * bb]) ++ coeffs
         modifyIORef memory $ Map.insert ka a
         modifyIORef memory $ Map.insert kb b
         modifyIORef memory $ Map.insert kab ab

       INPUT key s -> do
        x <- readChan p2f
        return ()

  -- Read requests from honest parties
  fork $ forever $ do
     (pid, pf) <- readChan p2f
     -- leak (pid,"Req")
     optionally $ do
          -- Return the write value
          writeChan f2p (pid, undefined)


fOpen :: MonadMPC_F m => Functionality () Fq a2f f2a z2f f2z m
fOpen (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Wait to collect shares from (t+1) honest parties
  shares <- newIORef Map.empty
  
  fork $ forever $ do
    (pid, sh) <- readChan p2f
    return ()

  return ()



fGetRand :: MonadMPC_F m => Functionality () Fq a2f f2a z2f f2z m
fGetRand (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Sample a random degree-t poly
  -- Send it to each party
  phi <- randomDegree ?t
  fork $ forever $ do
    (pid, ()) <- readChan p2f
    let i :: Integer = readNote pid "couldn't parse player number"
    writeChan f2p (pid, eval phi (toP i))
  return ()


fBeaverTriple :: (MonadMPC_F m, MonadOptionally m) => Functionality p2f f2p a2f f2a Void Void m
fBeaverTriple (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  -- Receive share from every honest party
  -- Sample a new polynomial
  optionally $ do
     undefined



envTestMPC :: MonadEnvironment m => Environment _ _ _ _ Void Void String m
envTestMPC z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
   -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("mpc","") empty

  fork $ forever $ do
    x <- readChan p2z
    liftIO $ putStrLn $ "Z: p sent " -- ++ show x
    ?pass

  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " -- ++ show m
    writeChan outp "environment output: 1"

  () <- readChan pump
  liftIO $ putStrLn "pump"
  writeChan z2p ("1", ())

  readChan pump


{- MPC Protocols -}

myID :: MonadMPC_P m => m Int
myID = let (i::Int) = readNote "pid" ?pid in return i

type MonadMPC_P m = (MonadProtocol m,
                     ?i :: Int,
                     ?n :: Int,
                     ?t :: Int)
