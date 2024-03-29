saUCy: Super Amazing Universal ComposabilitY
=====

A Haskell tour of the Universal Composability cryptography framework.

Universal Composability a general purpose framework for constructing, specifying, and analyzing cryptography protocols.

This project provides a concrete implementation of the framework, as a way of clarifying the ambiguous parts, experimenting with variations and extensions, and sanity-checking specifications, protocols, and simulator constructions.

Comparison with ILC-SaUCy:
The type system here provides only a partial checking. On the other hand, the tools and practicality of Haskell make this a convenient way to sanity check.

SaUCy is a research program that aims to use Universal Composability as the basis for software development tools. Goals of this include providing mechanically checkable proofs.

1. [InteractiveTuringMachines.hs](ProcessIO.hs)
   Defines the process model for interactive turing machines.

   A subset of the constraints of ILC are enforced by the type system here

2. [UniversalComposabilityStaticCorruptions.hs](StaticCorruptions.hs)

   Defines the UC execution experiment.

   The environment chooses a session ID, along with the list of parties to corrupt. Byzantine corruptions, since Adversary gets to send/receive all messages on behalf of the corrupted parties. Multiple parties with distinct PIDs are created on demand.

   Composition operator:  connects the Protocol-to-Functionality (`(p2f,f2p)`) channel of `pi` to Environment-to-Protocol (`(z2p,p2z)`) channel of `pi`
   Theorem: Composition preserves secure emulation
            (pi,F2) ~ (idealProtocol, F3)
            (rho,F1) ~ (idealProtocol, F2)
            ------------------------------------
            (pi o rho, F1) ~ (idealProtocol, F3)
            
   Theorem: Dummy Lemma - it's sufficient to prove against the dummy adversary each time

3. [Commitment.hs](Commitment.hs)

   Functionality: fCom, fRO
   Protocol: protCom

   Theorem: Commitment is realizable in the RO hybrid model
         fRO -> fCom

   Theorem: Commitment is impossible in the standard model, even if the parties are allowed to communicate

   TODO: fCom -> fCoinFlip

   TODO: Commitment using a CRS instead of fCom

4. [MultiPartyComputing.hs](MPC.hs)
   We model a reactive MPC service as an Arithmetic Black Box, that stores secret data and processes a sequence computations on that data. The sequence is comitted in a public log, the functionality ensures that it only leaks what's explicitly disclosed.
   We show how to use Beaver multiplication to extend a base MPC primitive (with just linear operations) to one with a MULT opcode.

   Functionality: fMPC, fABB 

   Theorem:
        fMPC_sansMult  ->  fMPC  -> fArithmeticBlackBox
   

4. [Multisession.hs](Multisession.hs)
   Composition operator: The `bangF` operator (!F) creates multiple instances of a functionality, each accessed by a sub-session id

   Theorem: Joint State composition
            !F -> !!F

5. [Authenticated Map.](AuthMap.hs)
   Optionally leak.
   (still TODO)
   
   fColRes -> fAuthMap 

6. [Async.hs](Async.hs)
   Composition operator: runAsyncF
   Composition operator: bangFAsync

7. [Multicast.hs]
   Functionality: fMulticast
   Protocol: protMulticast
   Theorem: Multicast is realizable in the !Auth model
      !fAuth -> fMulticast

   Application:  [ACast.hs](ACast.hs)

   Theorem: Bracha's protocol realizes fBroadcast

