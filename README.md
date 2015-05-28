saUCy: Super Amazing Universal ComposabilitY
=====

An implementation (in Haskell) of Universal Composability.

Universal Composability [cite] is a modern, general purpose framework for defining and implementing secure cryptographic protocols. However, it primarily exists only "on paper", and numerous variations (guc, juc, symbolic UC, RSIM, GNUC, and more) make it hard to keep track of the precise semantics of work done in UC.

This project provides a concrete implementation of the framework, as a way of clarifying the ambiguous parts, experimenting with variations and extensions, and sanity-checking specifications, protocols, and simulator constructions.

This is a component of a larger program to put Universal Composability on a proper analytic foundation, especially including mechanically checkable proofs. Other components will include a specialized programming language for UC, with a type checker that provides better guarantees, and integration with existing mechanized proof tools (like Easycrypt and Proverif)


