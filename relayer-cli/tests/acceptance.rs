//! Acceptance test: runs the application as a subprocess and asserts its
//! output for given argument combinations matches what is expected.
//!
//! Modify and/or delete these as you see fit to test the specific needs of
//! your application.
//!
//! For more information, see:
//! <https://docs.rs/abscissa_core/latest/abscissa_core/testing/index.html>

// Tip: Deny warnings with `RUSTFLAGS="-D warnings"` environment variable in CI

#![forbid(unsafe_code)]
#![warn(
    missing_docs,
    rust_2018_idioms,
    trivial_casts,
    unused_lifetimes,
    unused_qualifications
)]

use abscissa_core::testing::prelude::*;
use once_cell::sync::Lazy;

use relayer::config::{ChainConfig, Config};
use std::str::FromStr;
use tendermint::chain::Id;
use tendermint::net::Address;

/// Executes your application binary via `cargo run`.
///
/// Storing this value as a [`Lazy`] static ensures that all instances of
/// the runner acquire a mutex when executing commands and inspecting
/// exit statuses, serializing what would otherwise be multithreaded
/// invocations as `cargo test` executes tests in parallel by default.
pub static RUNNER: Lazy<CmdRunner> = Lazy::new(|| CmdRunner::default());

/// Configuration that connects to the informaldev/simd DockerHub image running on localhost.
fn simd_config() -> Config {
    let mut config = Config::default();
    config.chains = vec![ChainConfig {
        id: Id::from("ibc-test"),
        rpc_addr: Address::from_str("127.0.0.1:26657").unwrap(),
        account_prefix: "cosmos".to_string(),
        key_name: "testkey".to_string(),
        store_prefix: "ibc".to_string(),
        client_ids: vec!["ethbridge".to_string()],
        gas: 200000,
        trusting_period: Default::default(),
    }];
    config
}

/// Use `Config::default()` value if no config or args
#[test]
fn start_no_args() {
    let mut runner = RUNNER.clone();
    let mut cmd = runner.capture_stdout().run();
    cmd.stdout().expect_regex(
        format!(
            "^[^ ]*{} {}$",
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION")
        )
        .as_str(),
    ); // Todo: find out how to disable colored output and then remove the `[^ ]*` part from the regexp.
    cmd.wait().unwrap().expect_success();
}

/// Query connection ID. Requires the informaldev/simd Docker image running on localhost.
#[test]
#[ignore]
fn query_connection_id() {
    let mut runner = RUNNER.clone();
    let mut cmd = runner
        .config(&simd_config())
        .args(&["query", "connection", "end", "ibc-test", "connectionidone"])
        .capture_stdout()
        .run();
    // Todo: find out how to disable colored output
    // Local execution: (with color)
    //    cmd.stdout().expect_line("\u{1b}[0m\u{1b}[0m\u{1b}[1m\u{1b}[36m     Options\u{1b}[0m QueryConnectionOptions { connection_id: ConnectionId(\"connectionidone\"), height: 0, proof: true }", );
    // CI: (without color)
    cmd.stdout().expect_line("     Options QueryConnectionOptions { connection_id: ConnectionId(\"connectionidone\"), height: 0, proof: true }", );
    cmd.wait().unwrap().expect_success();
}

/// Query channel ID. Requires the informaldev/simd Docker image running on localhost.
#[test]
#[ignore]
fn query_channel_id() {
    let mut runner = RUNNER.clone();
    let mut cmd = runner
        .config(&simd_config())
        .args(&[
            "query",
            "channel",
            "end",
            "ibc-test",
            "firstport",
            "firstchannel",
        ])
        .capture_stdout()
        .run();
    // Todo: find out how to disable colored output
    // Local execution: (with color)
    //    cmd.stdout().expect_line("\u{1b}[0m\u{1b}[0m\u{1b}[1m\u{1b}[36m     Options\u{1b}[0m QueryChannelOptions { port_id: PortId(\"firstport\"), channel_id: ChannelId(\"firstchannel\"), height: 0, proof: true }", );
    // CI: (without color)
    cmd.stdout().expect_line("     Options QueryChannelOptions { port_id: PortId(\"firstport\"), channel_id: ChannelId(\"firstchannel\"), height: 0, proof: true }", );
    cmd.wait().unwrap().expect_success();
}

/// Query channel ID. Requires the informaldev/simd Docker image running on localhost.
#[test]
#[ignore]
fn query_client_id() {
    let mut runner = RUNNER.clone();
    let mut cmd = runner
        .config(&simd_config())
        .args(&["query", "client", "connections", "ibc-test", "clientidone"])
        .args(&["--proof", "false"])
        .capture_stdout()
        .run();
    // Todo: find out how to disable colored output
    // Local execution: (with color)
    //    cmd.stdout().expect_line("\u{1b}[0m\u{1b}[0m\u{1b}[1m\u{1b}[36m     Options\u{1b}[0m QueryClientConnectionsOptions { client_id: ClientId(\"clientidone\"), height: 0, proof: false }", );
    // CI: (without color)
    cmd.stdout().expect_line("     Options QueryClientConnectionsOptions { client_id: ClientId(\"clientidone\"), height: 0, proof: false }", );
    cmd.wait().unwrap().expect_success();
}
