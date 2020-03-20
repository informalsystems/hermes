# IBC Connection Handshake Spec

> Work in progress. Reviews are welcome.

## Specification roadmap

In this folder you will find a collection of documents representing English & TLA+ specifications for the IBC connection handshake problem [[ICS-003](https://github.com/cosmos/ics/tree/master/spec/ics-003-connection-semantics)].

We cover three levels of abstraction of the connection handshake, in accordance with the [VDD workflow](https://github.com/informalsystems/VDD/blob/master/manifesto/manifesto.md): _level 1_ (abstract), _level 2_ (system model & distributed protocol), and _level 3_ (single-node code).
Consequently, we break this work across the following documents:

- [L1_2.md](./L1_2.md) covers the highest level of abstraction (level 1) and also includes an English spec of the system model and protocol (level 2);
- [L2.tla](./L2.tla) is a TLA+ spec for level 2;
- [L3.tla](./L3.tla) is a TLA+ spec for level 3.

**[TODO: make sure this list is comprehensive.]**
**[TODO: cross-check terminology and language with the VDD articles; make sure we are consistent with VDD (e.g., "level" vs. "part", how to assign unique references and version to components, etc.)]**