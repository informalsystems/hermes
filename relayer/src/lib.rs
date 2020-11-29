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
// #![allow(dead_code, unreachable_code, unused_imports, unused_variables)]

//! IBC Relayer implementation

pub mod auth;
pub mod chain;
pub mod channel;
pub mod config;
pub mod connection;
pub mod error;
pub mod event;
pub mod foreign_client;
pub mod keyring;
pub mod keys;
pub mod light_client;
pub mod link;
pub mod msgs;
pub mod relay;
pub mod util;
