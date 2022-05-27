# IBC Relayer Integration Test Framework

## Overview

The `ibc-test-framework` crate provides the infrastructure and framework for writing end-to-end (E2E) tests that include the spawning of the relayer together with Cosmos full nodes running as child processes inside the tests.

## Installation

Other than Rust, the test suite assumes the `gaiad` binary is present in `$PATH`. You can install Gaia by either [building from source](https://github.com/cosmos/gaia), or load it using [Cosmos.nix](https://github.com/informalsystems/cosmos.nix/):

```text
nix shell github:informalsystems/cosmos.nix#gaia7
```

Alternatively, you can use `$CHAIN_COMMAND_PATH` to override with a different executable that is compatible with `gaiad`.

## Examples

Example tests written using `ibc-test-framework` can be found in the [`ibc-rs` project repository](https://github.com/informalsystems/ibc-rs/tree/master/tools/integration-test)

## Diagrams

Some diagrams have been prepared to ease the understanding of the test framework:

- [Tagged Identifiers and Data Structures](https://app.excalidraw.com/l/4XqkU6POmGI/7za2eSTChuT)
- [Test Data Structures](https://app.excalidraw.com/l/4XqkU6POmGI/5y6i0NKqiEv)
- [Test Framework Traits](https://app.excalidraw.com/l/4XqkU6POmGI/80KAnVZ6cu4)
