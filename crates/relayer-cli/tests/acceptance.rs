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

/// Executes your application binary via `cargo run`.
///
/// Storing this value as a [`Lazy`] static ensures that all instances of
/// the runner acquire a mutex when executing commands and inspecting
/// exit statuses, serializing what would otherwise be multithreaded
/// invocations as `cargo test` executes tests in parallel by default.
pub static RUNNER: Lazy<CmdRunner> = Lazy::new(CmdRunner::default);

/// Use `Config::default()` value if no config or args
#[cfg(not(tarpaulin))]
#[test]
fn start_no_args() {
    let mut runner = RUNNER.clone();
    let mut cmd = runner.capture_stdout().run();
    cmd.stdout().expect_regex(
        format!(
            "^[^ ]*{} {}",
            env!("CARGO_PKG_NAME"),
            regex::escape(env!("CARGO_PKG_VERSION"))
        )
        .as_str(),
    ); // Todo: find out how to disable colored output and then remove the `[^ ]*` part from the regexp.
    cmd.wait().unwrap().expect_success();
}

#[cfg(not(tarpaulin))]
#[test]
fn example_configuration_is_valid() {
    let mut runner = RUNNER.clone();
    let mut cmd = runner
        .capture_stdout()
        .args(["--config", "../config.toml", "config", "validate"])
        .run();
    cmd.stdout().expect_regex("configuration is valid");
    cmd.wait().unwrap().expect_success();
}
