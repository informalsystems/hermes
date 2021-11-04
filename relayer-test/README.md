# IBC Relayer Test Suite

## Overview

The `ibc-relayer-test` crate provides the infrastructure and framework for writing end-to-end (E2E) tests that include the spawning of the relayer together with Cosmos full nodes running as child processes inside the tests.

## Build Documentation

This documentation is best viewed as Rustdoc HTML pages. You can run the following command to build and view the documentation using `cargo doc`:

```bash
cargo doc -p ibc-relayer-test --open
```

## Installation

Other than Rust, the test suite assumes the `gaiad` binary is present in `$PATH`. You can install Gaia by either [building from source](https://github.com/cosmos/gaia), or load it using [Cosmos.nix](https://github.com/informalsystems/cosmos.nix/):

```text
nix shell github:informalsystems/cosmos.nix#gaia4
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

We first define an empty struct `ExampleTest` to represent our test case. We then implement the [`BinaryChannelTest`](crate::framework::binary::channel::BinaryChannelTest) trait so that the test framework sets up the relayer with two chains running together with connected channels.

Inside our test, we simply call the [`hang`](crate::hang) function to suspend the test indefinitely. While this means that the test would never pass, we can use this as a starting point to do _manual testing_ with the chains that have been setup by the test, and figure out how to continue writing our test.

Finally, we define the `example_test` with the `#[test]` pragma as the entry point for Rust to execute the test. We call the runner function [`run_binary_channel_test`](crate::framework::binary::channel::run_binary_channel_test), which accepts a reference to any struct implementing [`BinaryChannelTest`](crate::framework::binary::channel::BinaryChannelTest) and run the test for us.

By convention, the tests written are placed in the [`tests`](crate::tests) module. We can then run the test on the command line such as follows:

```bash
RUST_LOG=info RUST_BACKTRACE=1 \
    cargo test -p ibc-relayer-test -- --test-threads=1 \
    example_test
```

We use the environment variables `RUST_LOG` to control the log level, and `RUST_BACKTRACE` to display backtrace when errors occurred. The test flag `--test-threads=1` is set so that Rust do not run multiple tests in parallel, as it can make it difficult to follow the logs. Finally we specify the name of the test, which in our case is `example_test`, so that only that test is being run. See [TestConfig](crate::types::config::TestConfig) for more information about configuring how the tests should be run.

After starting the test, we may see the logs such as following shown:

```text
INFO ibc_relayer_test: starting test with test config: TestConfig { chain_command_path: "gaiad", chain_store_dir: "/path/to/data/test-2970732058", hang_on_fail: false }
INFO ibc_relayer_test: started new chain ibc-alpha-43044935 at with home path /path/to/data/test-2970732058/ibc-alpha-43044935 and RPC address http://localhost:56723.
INFO ibc_relayer_test: user wallet for chain ibc-alpha-43044935 - id: user1-34693377, address: cosmos1yyld4h2wwqz57dsqz4tmrmrsw6qw7unve884y5
INFO ibc_relayer_test: you can manually interact with the chain using commands starting with: gaiad --home '/path/to/data/test-2970732058/ibc-alpha-43044935' --node http://localhost:56723
...
INFO ibc_relayer_test: written hermes config.toml to /path/to/data/test-2970732058/config-61e5e82f.toml
...
WARN ibc_relayer_test: hanging the test indefinitely. you can still interact with any spawned chains and relayers
```

You can find in the logs information about how to manually interact with the chains that have been setup by the test. Near the last line of the logs, you can also find a warning that states that the test have been suspended indefinitely. We can also notice that the chains are created with random IDs and listening on random ports.

Using the log information, we can for example use `gaiad` to query for the balance of the accounts created by the test by running something like:

```bash
$ gaiad --home '/path/to/data/test-2970732058/ibc-alpha-43044935' \
    --node http://localhost:56723 query bank balances \
    cosmos1yyld4h2wwqz57dsqz4tmrmrsw6qw7unve884y5
balances:
- amount: "4397308370871"
  denom: coin42984fae
- amount: "4397308370871"
  denom: stake
pagination:
  next_key: null
  total: "0"
```

We can also see the data and configuration files generated in the absolute path shown in the log, which looks something like `/path/to/data/test-2970732058`. The sub-directory `test-2970732058` is randomly generated at the beginning of a test case, so that all data related to that test case belongs to the same directory.
