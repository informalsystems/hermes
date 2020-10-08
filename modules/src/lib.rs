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
//! - ICS 04: Channel
//! - ICS 07: Tendermint Client
//! - ICS 18: Basic relayer functions
//! - ICS 20: Fungible Token
//! - ICS 23: Vector Commitment Scheme
//! - ICS 24: Host Requirements
//! - ICS 26: Routing

pub mod context;
pub mod events;
pub mod handler;
pub mod ics02_client;
pub mod ics03_connection;
pub mod ics04_channel;
pub mod ics07_tendermint;
pub mod ics18_relayer;
pub mod ics20_fungible_token_transfer;
pub mod ics23_commitment;
pub mod ics24_host;
pub mod ics26_routing;
pub mod keys;
pub mod macros;
pub mod proofs;
pub mod tx_msg;

#[cfg(test)]
pub mod context_mock;

#[cfg(test)]
pub mod mock_client;

/// Height of a block, same as in `tendermint` crate
pub type Height = tendermint::block::Height;

#[cfg(test)]
mod test;

#[cfg(test)]
mod mock_context; // Context mock: for testing all handlers.
