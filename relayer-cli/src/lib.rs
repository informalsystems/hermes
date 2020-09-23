//! Cli for the IBC Relayer
//!
//! Application based on the [Abscissa] framework.
//!
//! [Abscissa]: https://github.com/iqlusioninc/abscissa

// Tip: Deny warnings with `RUSTFLAGS="-D warnings"` environment variable in CI

#![forbid(unsafe_code)]
#![deny(
    missing_docs,
    rust_2018_idioms,
    trivial_casts,
    unused_lifetimes,
    unused_qualifications
)]
#![allow(dead_code, unreachable_code, unused_imports, unused_variables)]

pub mod application;
pub mod commands;
pub mod config;
pub mod error;
pub mod prelude;
