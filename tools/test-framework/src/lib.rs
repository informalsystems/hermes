// #![deny(warnings)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::ptr_arg)]
#![doc = include_str!("../README.md")]

//!
//! ## Overview
//!
//! This IBC test framework gives developers working on relayer software in Rust a robust
//! yet flexible suite of functionality to test the correctness of their relayer implementations,
//! as well as verify the expected state of chains in response to relayed messages and packets.
//!
//! ## Example Test
//!
//! Here's an example of a simple test that showcases some of the important features that the
//! framework exposes:
//!
//! ```rust
//! use ibc_integration_test::prelude::*;
//!
//! pub struct ExampleTest;
//!
//! #[test]
//! pub fn example_test() -> Result<(), Error> {
//!     run_binary_channel_test(&ExampleTest)
//! }
//!
//! impl TestOverrides for ExampleTest {}
//!
//! impl BinaryChannelTest for ExampleTest {
//!     fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
//!         &self,
//!         _config: &TestConfig,
//!         _relayer: RelayerDriver,
//!         _chains: ConnectedChains<ChainA, ChainB>,
//!         _channel: ConnectedChannel<ChainA, ChainB>,
//!     ) -> Result<(), Error> {
//!         suspend()
//!     }
//! }
//! ```
//!
//! The `example_test` function is the top-most function that drives the test itself. The top-
//! most test function typically does nothing more than to specify what kind of test we want
//! to run. In the case of this example, we're running a
//! [`BinaryChannelTest`](ibc_test_framework::framework::binary::channel::BinaryChannelTest),
//! which sets up a relayer instance between two full nodes connected via IBC channels with
//! completed handshakes.
//!
//! Note that the `run_binary_channel_test` (and indeed every `run_*` test function) takes as
//! its single parameter an empty struct that represents the test case. In order to customize
//! the behavior of a test, different traits need to implemented on the empty struct, depending
//! on how you wish to modify the test.
//!
//! This example tests showcases implementing the `TestOverrides` trait, which is used to set
//! configuration and initialization values for the relayer instance that is being tested (in
//! this case though, nothing is being overriden).
//!
//! The main logic of the test is implemented in the `run` function of the `BinaryChannelTest`
//! trait. This trait is implemented for our empty test struct since we're choosing to run a
//! test between two chains connected via IBC channels. If we had instead opted to run a binary
//! _chain_ test using the `run_binary_chain_test`, then we would instead implement the
//! [`BinaryChainTest`](ibc_test_framework::framework::binary::chain::BinaryChannelTest)
//! trait for our empty test struct.
//!
//! The `run` function's parameters are:
//! 1. `config`: for accessing any relayer configuration values during the course of the test
//! 2. `relayer`: the relayer instance that is being tested
//! 3. `chains`: handles to the two chains, `ChainA` and `ChainB`, that are being relayed between
//! 4. `channel`: handles to the uni-directional channels connecting both ends of the two chains
//!
//! In this simple example test, the `run` function simply calls the [`suspend`] function,
//! which suspends the test indefinitely. While this means the test will never actually
//! pass, we can use this as a starting point in order to perform _manual testing_ with
//! the chains that have been set up in the test.
//!
//! ## Running Tests
//! By convention, tests are written to the [`tests`](ibc_test_framework::tests) module. We
//! can then run the test via the command line as follows:
//!
//! ```bash
//! RUST_LOG=info RUST_BACKTRACE=1 \
//!     cargo test -p ibc-relayer-test --features example -- --test-threads=1 \
//!     example_test
//! ```
//!
//! The environment variable RUST_LOG controls the log level. The RUST_BACKTRACE variable
//! displays a backtrace when errors occur in a test. The test flag `--test-threads=1` is
//! set so that tests are run serially (this makes it easier to follow what is going on
//! via the log output). Take a look at the [`TestConfig`](ibc_test_framework::types::config::TestConfig)
//! type for more information about configuring how tests can be run.
//!
//! For this example, we disable the test from running by default, since it calls the
//! [`suspend`] function and will thus never pass. We explicitly pass `--features example`
//! so that the `example` feature is activated such that this test will run. Finally, we
//! specify the name of the test so that _only_ our example test is run.
//!
//! After starting the test run, we may see logs such as the following:
//!
//! ```text
//! $ cargo test -p ibc-integration-test --features example -- --nocapture --test-threads=1 example_test
//! ...
//! INFO created new chain/client/connection/channel from ibc-alpha-c4aed8f9/07-tendermint-4/connection-6/channel-1 to ibc-beta-fcb867bb/07-tendermint-6/connection-1/channel-6
//! INFO written channel environment to /path/to/ibc-rs/tools/integration-test/data/test-1094235493/binary-channels.env
//! WARN suspending the test indefinitely. you can still interact with any spawned chains and relayers
//! ...
//! ```
//!
//! The INFO lines are notifying us of the path environment variables exported by the test.
//! The WARN line states that the test has been suspended indefinitely, as we knew it would.
//! Note that the chains are created with random IDs and are listening on random ports.
//!
//! Using the logs, we can for example use `gaiad` to query for the balance of the accounts
//! created by the test by running:
//!
//! ```bash
//! $ source /path/to/ibc-rs/tools/integration-test/data/test-1094235493/binary-channels.env
//! $ gaiad --home "$NODE_A_HOME" --node $NODE_A_RPC_ADDR query bank balances $NODE_A_WALLETS_USER1_ADDRESS
//! balances:
//! - amount: "6902395390297"
//! denom: coin95143d31
//! - amount: "6902395390297"
//! denom: stake
//! pagination:
//! next_key: null
//! total: "0"
//! ```
//!
//! The test data and configuration files are stored at the absolute path shown in the
//! log, which looks something like `/path/to/ibc-rs/tools/integration-test/data/test-1094235493`.
//! The sub-directory `test-1094235493` is randomly generated at the beginning of a test
//! case such that all data related to that test lives in the same directory.

extern crate alloc;

pub mod bootstrap;
pub mod chain;
pub mod error;
pub mod framework;
pub mod ibc;
pub mod prelude;
pub mod relayer;
pub mod types;
pub mod util;
