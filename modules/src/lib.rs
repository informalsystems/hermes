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
//! The layout of this crate mirrors the classifications of the [Interchain
//! Standards][ics-standards]. These classifications are [Core][core], [Clients][clients],
//! [Applications][applications], and [Relayer][relayer].
//!
//! Core consists of the designs and logic pertaining to the transport, authentication, and
//! ordering layers of the IBC protocol, the most fundamental pieces.
//!
//! Clients consists of the implementations of various state machine front-ends that leverage the
//! IBC protocol.
//!
//! Applications consists of various packet encoding and processing semantics which underpin the
//! various types of transactions that users can perform on any IBC-compliant chain.
//!
//! Relayer contains an important off-chain process, the Hermes packet relayer, which is
//! responsible for facilitating communication between sovereign blockchains via packet forwarding.
//!
//! [core]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/core
//! [clients]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/clients
//! [applications]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/applications
//! [relayer]: https://github.com/informalsystems/ibc-rs/tree/master/modules/src/relayer
//! [ics-standards]: https://github.com/cosmos/ibc#interchain-standards

extern crate alloc;
extern crate std;

mod prelude;

pub mod applications;
pub mod clients;
pub mod core;
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
