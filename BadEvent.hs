 {-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ScopedTypeVariables, OverlappingInstances, MultiParamTypeClasses
  
  #-} 

{-
  Here we develop a general framework for Bad Events.

  We define functionalities making use of a new instruction "throwBadEvent" to assert cases that should not occur. The enviroment is immediately notified when a bad event occurs. For example, a "collision resistant hash" functionality may be parameterized by an arbitrary function, but throws a BadEvent whenever a collision is detected.

  When we prove that a protocol realizes such a functionality, our real world assumptions will typically prevent the adversary from causing any bad events. This strengthens the emulation theorem, since it forces the simulator also not to trigger a bad event.

  When using the functionality in a hybrid protocol, we will assume that bad events do not occur. More concretely, when proving a simulator matches the dummy adversary, we will typically reduce any error in simulation can reduce to triggering a BadEvent in the protocol.


  Several composition theorems make it easier to work with functionalities defined using BadEvents. As an example, consider the case of Signature functionalities, which can be effectively defined this way. We will eventually realize the Signature functionality using a cryptographic signature scheme and an ordinary PKI functionality (which does not define any BadEvents); we will also make use of the Signature functionality in distributed systems protocols, such as authenticated broadcast (the specifications for which also do not define any BadEvents).

           signature algorithm                broadcast protocol
     PKI -----------------------> Signature ----------------------> Broadcast


  In this case, the BadEvents are only relevant to the intermediate Signature definition - the security definitions of the composed protocol do not rely o them. The following definition and composition theorem can be used to eliminate the BadEvents layer in cases like this, resulting in a plain security theorem.

  Definition:
       an F-hybrid protocol pi realizes G "except for bad events in F" iff
        forall A. exists S. forall Z. 
           result <- (execUC Z pi F A)
           conditioned( fromGoodRun result | hasBadEvent result )
           ~ 
           execUC Z idealProtocol G S


  Composition Theorem:
       F and H do not have bad events. G may have bad events.
       (pi, noBadEvents F) realizes G 
       (rho,G) realizes H except for bad events in G
       ----------------------------
       (rho^pi,F) realizes H
       


  A second composition theorem.... TODO

  Definition:
       an F-hybrid protocol pi is "free of bad events" if 
          forall A. forall Z. hasBadEvent (execUC Z pi F A) == False with high probability

  Composition Theorem 2:
       F and G may have bad events. H does not have bad events.
       (pi,F) is free of bad events
       (pi,F) realizes G
       (rho,G) realizes H except for bad events in G
       ----------------------------
       (rho^pi,F) is free of bad events
       (rho^pi,F) realizes H except for bad events in F

  
-}

module BadEvent where

import ProcessIO
import StaticCorruptions
import Duplex
import Clock

import Control.Concurrent.MonadIO
import Control.Monad (forever, forM_, replicateM_)
import Control.Monad.Reader

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map

runBadEventF :: (HasFork m) =>
     (Crupt
      -> (Chan (PID, p2f), Chan (PID, f2p))
      -> (Chan a2f, Chan f2a)
      -> (Chan z2f, Chan f2z)
      -> AsyncFuncT (DuplexT ClockPeerIn ClockPeerOut m) ())
     Crupt
     -> (Chan (PID, p2f), Chan (PID, MulticastF2P t))
     -> (Chan (MulticastA2F t), Chan (MulticastF2A t))
     -> (c, d)
     -> m ()

runBadEventF :: (HasFork m, MonadSID m) =>
     (Map PID ()
      -> (Chan (PID, t3), Chan (PID, b))
      -> (Chan a2f, Chan f2a)
      -> (Chan z2f, Chan f2z)
      -> AsyncFuncT (DuplexT ClockPeerIn ClockPeerOut m) ())
     -> Map PID ()
     -> (Chan (PID, DuplexP2F Void t3), Chan (PID, DuplexF2P Void b))
     -> (Chan (DuplexA2F ClockA2F a2f), Chan (DuplexF2A ClockF2A f2a))
     -> (Chan (DuplexZ2F ClockZ2F z2f), Chan (DuplexF2Z ClockF2Z f2z))
     -> m ()

runErrorP = do
  
