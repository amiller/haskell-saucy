saUCy: Super Amazing Universal ComposabilitY
=====

A Haskell tour of the Universal Composability cryptography framework.

Universal Composability a general purpose framework for constructing, specifying, and analyzing cryptography protocols.

This project provides a concrete implementation of the framework, as a way of clarifying the ambiguous parts, experimenting with variations and extensions, and sanity-checking specifications, protocols, and simulator constructions.

Comparison with ILC-SaUCy:
The type system here provides only a partial checking. On the other hand, the tools and practicality of Haskell make this a convenient way to sanity check.

SaUCy is a research program that aims to use Universal Composability as the basis for software development tools. Goals of this include providing mechanically checkable proofs.

1. InteractiveTuringMachines.hs
   Defines the process model for interactive turing machines.

   A subset of the constraints of ILC are enforced by the type system here

2. UniversalComposabilityStaticCorruptions.hs

   Defines the UC execution experiment.

   The environment chooses a session ID, along with the list of parties to corrupt. Byzantine corruptions, since Adversary gets to send/receive all messages on behalf of the corrupted parties. Multiple parties with distinct PIDs are created on demand.

   Composition operator:  connects the Protocol-to-Functionality (`(p2f,f2p)`) channel of `pi` to Environment-to-Protocol (`(z2p,p2z)`) channel of `pi`
   Theorem: Composition preserves secure emulation
            (pi,F2) ~ (idealProtocol, F3)
            (rho,F1) ~ (idealProtocol, F2)
            ------------------------------------
            (pi o rho, F1) ~ (idealProtocol, F3)
            
   Theorem: Dummy Lemma - it's sufficient to prove against the dummy adversary each time

3. Commitment.hs

   Functionality: fCom, fRO
   Protocol: protCom

   Theorem: Commitment is impossible in the standard model, even if the parties are allowed to communicate

   Theorem: Commitment is realizable in the RO hybrid model
         fRO -> fCom

4. Multisession.hs
   Composition operator: The `bangF` operator (!F) creates multiple instances of a functionality, each accessed by a sub-session id

   Theorem: Joint State composition
            !F -> !!F

5. Async.hs
   Composition operator: runAsyncF
   Composition operator: bangFAsync

6. Multicast.hs
   Functionality: fMulticast
   Protocol: protMulticast
   Theorem: Multicast is realizable in the !Auth model
      !fAuth -> fMulticast

7. ACast.hs

   Theorem: Bracha's protocol realizes fBroadcast
