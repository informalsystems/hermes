#![forbid(unsafe_code)]
#![deny(
    trivial_casts,
    trivial_numeric_casts,
    unused_import_braces,
    unused_qualifications,
    rust_2018_idioms
)]

//! IBC Relayer implementation as a library.
//!
//! For the IBC relayer binary, please see [Hermes] (`ibc-relayer-cli` crate).
//!
//! [Hermes]: https://docs.rs/ibc-relayer-cli/0.2.0/

#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate rouille;

pub mod chain;
pub mod channel;
pub mod config;
pub mod connection;
pub mod error;
pub mod event;
pub mod foreign_client;
pub mod keyring;
pub mod light_client;
pub mod link;
pub mod macros;
pub mod object;
pub mod registry;
pub mod relay;
pub mod supervisor;
pub mod telemetry;
pub mod transfer;
pub mod upgrade_chain;
pub mod util;
pub mod worker;
