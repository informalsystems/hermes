// TODO: disable unwraps:
// https://github.com/informalsystems/ibc-rs/issues/987
// #![cfg_attr(not(test), deny(clippy::unwrap_used))]

#![no_std]
#![allow(clippy::large_enum_variant)]
#![deny(
    warnings,
    // missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unused_import_braces,
    unused_qualifications,
    rust_2018_idioms
)]
#![forbid(unsafe_code)]

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

extern crate alloc;
extern crate std;

mod prelude;

pub mod applications;
pub mod core;
pub mod clients;
pub mod events;
pub mod handler;
pub mod keys;
pub mod macros;
pub mod proofs;
pub mod query;
pub mod relayer;
pub mod signer;
pub mod timestamp;
pub mod tx_msg;

mod serializers;

/// Re-export of ICS 002 Height domain type
pub type Height = crate::core::ics02_client::height::Height;

#[cfg(test)]
mod test;

#[cfg(any(test, feature = "mocks"))]
pub mod test_utils;

#[cfg(any(test, feature = "mocks"))]
pub mod mock; // Context mock, the underlying host chain, and client types: for testing all handlers.
