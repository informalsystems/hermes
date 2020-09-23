#![forbid(unsafe_code)]
#![deny(
    // warnings,
    // missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unused_import_braces,
    unused_qualifications,
    rust_2018_idioms
)]
#![allow(dead_code, unreachable_code, unused_imports, unused_variables)]

//! IBC Relayer implementation

pub mod chain;
pub mod client;
pub mod config;
pub mod error;
pub mod event_handler;
pub mod event_monitor;
pub mod store;
pub mod util;
