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

//! Implementation of the following ICS modules:
//!
//! - ICS 02: Client
//! - ICS 03: Connection
//! - ICS 04: Channel
//! - ICS 05: Port
//! - ICS 07: Tendermint Client
//! - ICS 18: Basic relayer functions
//! - ICS 23: Vector Commitment Scheme
//! - ICS 24: Host Requirements
//! - ICS 26: Routing
//! - Applications:
//!    - ICS 20: Fungible Token Transfer
pub mod address;
pub mod application;
pub mod events;
pub mod handler;
pub mod ics02_client;
pub mod ics03_connection;
pub mod ics04_channel;
pub mod ics05_port;
pub mod ics07_tendermint;
pub mod ics18_relayer;
pub mod ics23_commitment;
pub mod ics24_host;
pub mod ics26_routing;
pub mod keys;
pub mod macros;
pub mod proofs;
pub mod tx_msg;

mod serializers;

/// Re-export of ICS 002 Height domain type
pub type Height = crate::ics02_client::height::Height;

#[cfg(test)]
mod test;

#[cfg(any(test, feature = "mocks"))]
pub mod test_utils;

#[cfg(any(test, feature = "mocks"))]
pub mod mock; // Context mock, the underlying host chain, and client types: for testing all handlers.
