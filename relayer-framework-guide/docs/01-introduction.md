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
