#![forbid(unsafe_code)]
#![deny(clippy::all)]
#![deny(
    warnings,
    // missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unused_import_braces,
    unused_qualifications,
    rust_2018_idioms
)]
#![allow(dead_code)]

//! Implementation of the following ICS modules:
//!
//! - ICS 02: Client
//! - ICS 03: Connection
//! - ICS 07: Tendermint Client
//! - ICS 23: Vector Commitment Scheme
//! - ICS 24: Host Requirements

pub mod error;
pub mod events;
pub mod ics02_client;
pub mod ics03_connection;
pub mod ics04_channel;
pub mod ics07_tendermint;
pub mod ics20_fungible_token_transfer;
pub mod ics23_commitment;
pub mod ics24_host;
pub mod keys;
pub mod path;
pub mod proofs;
pub mod query;
pub mod tx_msg;

/// Height of a block, same as in `tendermint` crate
pub type Height = tendermint::lite::Height;

#[cfg(test)]
mod test;
