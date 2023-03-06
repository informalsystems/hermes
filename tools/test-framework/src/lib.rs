// #![deny(warnings)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::ptr_arg)]
#![doc = include_str!("../README.md")]

//! ## Overview
//!
//! This IBC test framework gives developers working on relayer software in Rust a robust
//! yet flexible suite of functionality to test the correctness of their relayer implementations,
//! as well as verify the expected state of chains in response to relayed messages and packets.
//!
//! ## Running Tests
//!
//! We can run tests via the command line as follows:
//!
//! ```bash
//! RUST_LOG=info RUST_BACKTRACE=1 \
//!     cargo test -p ibc-integration-test --features example -- --test-threads=1 \
//!     example_test
//! ```
//!
//! The environment variable `RUST_LOG` controls log filtering for Hermes and,
//! besides the global log level, can be used to pass more elaborate directives
//! for the tracing framework. The `RUST_BACKTRACE` variable
//! displays a backtrace when errors occur in a test. The test flag `--test-threads=1` is
//! set so that tests are run serially (this makes it easier to follow what is going on
//! via the log output). Take a look at the [`TestConfig`](crate::types::config::TestConfig)
//! type for more information about configuring how tests can be run.
//!
//! For this example, we disable the test from running by default, since it calls the
//! `suspend` function and will thus never pass. We explicitly pass `--features example`
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
pub mod docs;
pub mod error;
pub mod framework;
pub mod ibc;
pub mod prelude;
pub mod relayer;
pub mod types;
pub mod util;
