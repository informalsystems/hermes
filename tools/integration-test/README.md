# IBC Relayer Integration Test Suite

## Overview

The `ibc-relayer-test` crate provides the infrastructure and framework for writing end-to-end (E2E) tests that include the spawning of the relayer together with Cosmos full nodes running as child processes inside the tests.

## Build Documentation

This documentation is best viewed as Rustdoc HTML pages. You can run the following command to build and view the documentation using `cargo doc`:

```bash
cargo doc -p ibc-integration-test --open
```

## Installation

Other than Rust, the test suite assumes the `gaiad` binary is present in `$PATH`. You can install Gaia by either [building from source](https://github.com/cosmos/gaia), or load it using [Cosmos.nix](https://github.com/informalsystems/cosmos.nix/):

```text
nix shell github:informalsystems/cosmos.nix#gaia4
```

## Quick Start

See [`tests::example`](crate::tests::example) for an example test with
access to a full test setup.
