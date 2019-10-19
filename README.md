saUCy: Super Amazing Universal ComposabilitY
=====

An implementation (in Haskell) of Universal Composability.

Universal Composability [cite] is a modern, general purpose framework for defining and implementing secure cryptographic protocols. However, it primarily exists only "on paper", and numerous variations (guc, juc, symbolic UC, RSIM, GNUC, and more) make it hard to keep track of the precise semantics of work done in UC.

This project provides a concrete implementation of the framework, as a way of clarifying the ambiguous parts, experimenting with variations and extensions, and sanity-checking specifications, protocols, and simulator constructions.

This is a component of a larger program to put Universal Composability on a proper analytic foundation, especially including mechanically checkable proofs. Other components will include a specialized programming language for UC, with a type checker that provides better guarantees, and integration with existing mechanized proof tools (like Easycrypt and Proverif)

1. InteractiveTuringMachines.hs
   Defines the process model for interactive turing machines.

   A subset of the constraints of ILC are enforced by the type system here

2. UniversalComposabilityStaticCorruptions.hs

   Defines the UC execution experiment.

   Session ID chosen by the environment. Multiple parties created on demand

   Composition operator, connects the Protocol-to-Functionality (`(p2f,f2p)`) channel of `pi` to Environment-to-Protocol (`(z2p,p2z)`) channel of `pi`
   Theorem: Composition preserves secure emulation
            (pi,F2) ~ (idealProtocol, F3)
            (rho,F1) ~ (idealProtocol, F2)
            ------------------------------------
            (pi o rho, F1) ~ (idealProtocol, F3)
            
   Theorem: Dummy Lemma - it's sufficient to prove against the dummy adversary each time

3. Commitment.hs

   Theorem: Commitment is impossible in the standard model, even if the parties are allowed to communicate

   Theorem: Commitment is realizable in the RO hybrid model

4. Multisession.hs

   The `bangF` operator (!F) creates multiple instances of a functionality, each accessed by a sub-session id

   Theorem: Joint State composition

5. Async.hs

   Theorem: 

6. Multicast.hs

   Theorem: Multicast is realizable in the !Auth model

7. ACast.hs

   Theorem: Bracha's protocol realizes fBroadcast