# IBC Connection Handshake Spec

> Work in progress. Reviews are welcome.

## Specification roadmap

In this folder you will find a collection of documents representing English & TLA+ specifications for the IBC connection handshake problem [[ICS-003](https://github.com/cosmos/ics/tree/master/spec/ics-003-connection-semantics)].


We currently cover two levels of abstraction of ICS2, in accordance with the [VDD workflow](https://github.com/informalsystems/VDD/blob/master/manifesto/manifesto.md): _level 1_ (abstract), _level 2_ (system model & distributed protocol).
Consequently, we break this work across the following documents:

- [L1_2.md](./L1_2.md) covers the highest level of abstraction (level 1) and also includes an English spec of the system model and protocol (level 2);
- [L2-tla](./L2-tla/) is a directory with the TLA+ spec for level 2.