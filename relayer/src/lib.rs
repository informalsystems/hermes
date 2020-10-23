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

pub mod auth;
pub mod chain;
pub mod channel;
pub mod client;
pub mod config;
pub mod connection;
pub mod keyring;
pub mod error;
pub mod event_handler;
pub mod event_monitor;
pub mod foreign_client;
pub mod link;
pub mod msgs;
pub mod tx;
pub mod util;
pub mod keys;
