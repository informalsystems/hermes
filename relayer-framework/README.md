# `ibc-relayer-framework`

# Overview

The `ibc-relayer-framework` crate provides an abstract interface for implementing
IBC relayers, with _zero_ dependency to concrete chain definitions. Using traits
and associated types, the relayer framework allows various dependencies of the
relayer to be loaded via dependency injection without requiring global dependencies
to be specified.

Using the relayer framework, different chain implementations can be instantiated
by defining the concrete type definitions and methods for communicating with the
blockchain. Relaying between different chain implementations is made possible by
having abstract relaying logic, which can be instantiated along with the concrete
chain implementations.

# Problem Statement

The IBC relayer framework is designed to solve multiple problems simultaneously:

- The need for multiple relaying strategies, including cross-cutting concerns for:
  - Update client mechanics
  - Message batching
  - Error retry
  - Logging
  - Telemetrics
  - Caching

- Handling differences in protobuf definitions and behavior arise from different Cosmos
  chain implementations:
  - Tendermint
  - Cosmos SDK
  - ibc-go

- Handling relaying from non-Cosmos SDK chains
  - Nomic
  - Penumbra

- Handling relaying from non-Cosmos chains
  - Substrate

The relayer framework solves all problems by separating out each concern
as different components that can be specified independently. With dependency
injection, each component can independently specify the dependency it needs
from the surrounding context, and composition of components can be done
without knowing the detailed dependency of each component.

# Technical Background

A [technical background](crate::docs::technical_background) is provided to
help readers understand the techniques used by the relayer framework to
compose various components together. It is highly recommended for readers
of all level of expertise to read the document before continue reading
the code and documentation.
