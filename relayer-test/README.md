# IBC Relayer Test Suite

## Overview

The `ibc-relayer-test` crate provides the infrastructure and framework for writing end-to-end (E2E) tests that include the spawning of the relayer together with Cosmos full nodes running as child processes inside the tests.

## Build Instruction

This documentation is best viewed as Rustdoc HTML pages. You can run the following command to build and view the documentation using `cargo doc`:

```bash
cargo doc -p ibc-relayer-test --open
```

## Quick Start

A quick way of getting started is to write a simple test that includes the full test setup and does nothing but just hang the test:

```rust
use ibc_relayer_test::prelude::*;

struct ExampleTest;

impl TestOverrides for ExampleTest {}

impl BinaryChannelTest for ExampleTest {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        _chains: &ConnectedChains<ChainA, ChainB>,
        _channel: &Channel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        hang()
    }
}

#[test]
fn example_test() -> Result<(), Error> {
    run_binary_channel_test(&ExampleTest)
}
```

By convention, the tests written are placed in the [`tests`](crate::tests) module. We can then run the test on the command line such as follows:

```bash
RUST_LOG=info RUST_BACKTRACE=1 \
    cargo test -p ibc-relayer-test -- --nocapture --test-threads=1 \
    example_test
```



```text
INFO ibc_relayer_test: started new chain ibc-alpha-43044935 at with home path /path/to/data/ibc-alpha-43044935 and RPC address http://localhost:56723.
INFO ibc_relayer_test: user wallet for chain ibc-alpha-43044935 - id: user1-34693377, address: cosmos1yyld4h2wwqz57dsqz4tmrmrsw6qw7unve884y5
INFO ibc_relayer_test: you can manually interact with the chain using commands starting with: gaiad --home '/path/to/data/ibc-alpha-43044935' --node http://localhost:56723
...
INFO ibc_relayer_test: written hermes config.toml to /path/to/data/relayer/config-61e5e82f.toml
...
WARN ibc_relayer_test: hanging the test indefinitely. you can still interact with any spawned chains and relayers
```
