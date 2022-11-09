# ADR 012: New Relayer Architecture

## Changelog

* 2022-11-10: Initial Draft

## Context and Problem Statement

The current Hermes relayer, hereby called V1 relayer in this document, was
implemented at a time when the Cosmos ecosystem was still very new, and the
idea of cross-chain with IBC was still a novel concept. The Hermes relayer
has a monumental contribution toward the success of IBC and Cosmos, and it
is the most widely used IBC relayer in the Cosmos ecosystem today.

The adoption of Interchain and IBC continues to grow, and IBC traffic is
increasing at an expoential pace. From our experience in developing and
operating the Hermes relayer, we have learned many valuable lessons about
the challenges of building a reliable IBC relayer for a modern Interchain
ecosystem.

In this section, we will share some of the challenges that the V1 Hermes
relayer faces, and the motivation for why there is a need to rethink about
the IBC relayer architecture.

### Support for non-SDK and non-Cosmos Chains

The success of IBC and the growth of Interchain introduce new use cases that
the V1 relayer did not sufficiently focus on. For example, we have received
many feature requests from Substrate to modify the Hermes code base to better
support relaying between a Cosmos chain and a Substrate chain.

### Support for mutiple versions of Cosmos chain


### Support for multiple batching strategies


### Async Concurrency


### Type safety for differentiation of identifiers from different chains

### Code correctness and formal verification


## Decision

### Development Plan

The Hermes V2 relayer is designed from the top down with a new architecture
that is compatible with existing code base. This reduces the risk of having
a complete rewrite from the ground up, which may take too long and may fail
to deliver.

We progress toward the relayer v2 design with an MVP, called relayer v1.5,
which adds a small number of experimental features to the existing v1 relayer
without replacing existing features of the v1 relayer. In contrast, a v2
relayer is expected to supercede the majority features of the v1 relayer
with new and improved code.

For the purpose of the architecture re-design, all the new code being
developed are targetted toward the relayer v2. But the new code will be
usable in the form of experimental features when the relayer v1.5 is
released. Both the v1 relayer and the new relayer will co-exist from
v1.5 onward, until the v2 relayer is released.

In the relayer v1.5 MVP, the new relayer only re-implements the packet
worker and the transaction sender. With that, the new relayer does not
depend on the `RelayPath` and `Link` data types, as well as the `send_tx`
methods in the v1 relayer. In contrast, the new relayer will initially
continue to rely on the `ForeignClient` and `ChainHandle` datatypes
to perform queries and processing of messages.

### Architecture Overview

A full description of the relayer v2 architecture is too much to be described
in this ADR. Instead, readers are encouraged to read the full documentation
from the generated Cargo docs for the new relayer crates.

At its core, the v2 relayer makes use of a new programming technique, called
_context-generic programming_ (CGP), to implement the relayer components in a
modular fashion. CGP turns OOP methods into modular components by replacing
the concrete `Self` type with a _generic_ `Context` type. Using the special
properties of Rust's trait system, CGP allows component implementations to
add new constraints and requirements to the `Context` type through `where`
clauses inside `impl` blocks, by which the constraints would automatically
propagated to the top level without having to repeatedly specify the
constraints at every level of the code.

Using CGP, the core logic of the new relayer is implemented as a fully
abstract library crate called `ibc-relayer-framework`, with no dependency
to external crates except for using the `async-trait` crate to support
async functions inside traits. In addition, the relayer framework is
developed with `#![no_std]` enabled. By having almost no external dependency,
the relayer can be ported to various restrictive environments, such as
Wasm, Substrate runtime, and symbolic execution environments.


## Status

Proposed

## Consequences

## Positive

## Negative

## Neutral

## References
