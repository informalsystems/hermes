# Introduction

## Overview

The `ibc-relayer-framework` crate provides an abstract interface for implementing
IBC relayers, with _zero_ dependency on concrete chain definitions. Using traits
and associated types, the relayer framework allows various dependencies of the
relayer to be loaded via dependency injection without requiring global dependencies
to be specified.

Using the relayer framework, different chain implementations can be instantiated
by defining the concrete type definitions and methods for communicating with the
blockchain. Relaying between different chain implementations is made possible by
having abstract relaying logic, which can be instantiated along with the concrete
chain implementations.

## Problem Statement

The IBC relayer framework is designed to solve multiple problems simultaneously:

- The need for multiple relaying strategies, including cross-cutting concerns for:
  - Updating client mechanics
  - Message batching
  - Retrying on errors
  - Logging
  - Telemetrics
  - Caching

- Handling differences in protobuf definitions and behavior that arise from different Cosmos
  chain implementations such as:
  - Tendermint
  - Cosmos SDK
  - ibc-go

- Handling relaying from non-Cosmos SDK chains, such as:
  - Nomic
  - Penumbra

- Handling relaying from non-Cosmos chains, such as:
  - Substrate

The relayer framework solves all these problems by separating out each concern
into different components that can be specified independently. With dependency
injection, each component can independently specify the dependency it needs
from the surrounding context, and composition of components can be done
without knowing the detailed dependency of each component.
