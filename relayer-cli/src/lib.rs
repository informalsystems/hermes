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
#![allow(unused_variables)]

pub mod application;
pub mod commands;
pub mod config;
pub mod error;
pub mod prelude;
pub mod registry;

pub(crate) mod cli_utils;
pub(crate) mod components;
pub(crate) mod conclude;
pub(crate) mod entry;
