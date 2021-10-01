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

//! This library implements the _I_nter_B_lockchain _C_ommunication (IBC) protocol in Rust. IBC is
//! a distributed protocol that enables communication between distinct sovereign blockchains.
//! Loose analogies may be drawn between the IBC protocol and the TCP/UDP protocols that enable
//! communication over the internet via packet streaming. Indeed, IBC also encodes the notion of
//! ordered and unordered packet streams.
//!
//! At its highest level, IBC can be categorized into on-chain modules and off-chain processes.
//! On-chain modules, so called because they are the building blocks upon which IBC chains are
//! built, is where the main data structures and abstractions of the IBC protocol reside. These 
//! abstractions, sometimes also referred to as 'handlers', are specified in _I_nter_C_hain 
//! _S_tandards (ICSs), which can be found [here][ibc-standards]. 
//!
//! The main IBC handlers are `Client`s, `Connection`s, and `Channel`s:
//! - `Client`s ([ICS 02][ics02]) encapsulate encapsulate the verification methods of another
//! IBC-enabled chain in order to ensure that the other chain adheres to the IBC protocol and does
//! not exhibit any misbehavior.
//! - `Connection`s ([ICS 03][ics03]) associate a chain with another chain by connecting a `Client`
//! on the local chain with a `Client` on the remote chain.
//! - `Channel`s ([ICS 04][ics04]) ensure, among other things, that packets sent between connected
//! chains are well-ordered.
//!
//! [ics02]: https://github.com/cosmos/ibc/blob/master/spec/core/ics-002-client-semantics/README.md
//! [ics03]: https://github.com/cosmos/ibc/tree/master/spec/core/ics-003-connection-semantics
//! [ics04]: https://github.com/cosmos/ibc/tree/master/spec/core/ics-004-channel-and-packet-semantics
//! [ics-standards]: https://github.com/cosmos/ibc#interchain-standards

extern crate alloc;
extern crate std;

mod prelude;

pub mod application;
pub mod events;
pub mod handler;
pub mod keys;
pub mod macros;
pub mod proofs;
pub mod query;
pub mod signer;
pub mod timestamp;
pub mod tx_msg;

pub mod ics02_client;
pub mod ics03_connection;
pub mod ics04_channel;
pub mod ics05_port;
pub mod ics07_tendermint;
pub mod ics18_relayer;
pub mod ics23_commitment;
pub mod ics24_host;
pub mod ics26_routing;

mod serializers;

/// Re-export of ICS 002 Height domain type
pub type Height = crate::ics02_client::height::Height;

#[cfg(test)]
mod test;

#[cfg(any(test, feature = "mocks"))]
pub mod test_utils;

#[cfg(any(test, feature = "mocks"))]
pub mod mock; // Context mock, the underlying host chain, and client types: for testing all handlers.
