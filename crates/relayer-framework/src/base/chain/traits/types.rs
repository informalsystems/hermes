//! The base chain contexts upon which higher level chain contexts such as
//! `OfaBaseChain` are composed from.
//!
//! These traits can be implemented over the default `OfaBaseChain` trait if the
//! behavior exposed by that trait and the `AfoBaseChain` trait are not desired.

use crate::base::core::traits::error::HasError;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasMessageType: Async {
    type Message: Async;
}

pub trait HasEventType: Async {
    type Event: Async;
}

/// The minimal datatypes that any chain needs to expose.
pub trait HasChainTypes: HasMessageType + HasEventType + HasError {
    type Height: Ord + Async;

    type Timestamp: Ord + Async;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error>;
}

/// The datatypes that IBC chains need to expose in addition to the datatypes
/// exposed by the base `ChainContext`.
///
/// Each [`HasIbcChainTypes`] is parameterized by a `Counterparty` chain
/// which must also implement the `ChainContext` trait.
pub trait HasIbcChainTypes<Counterparty>: HasChainTypes
where
    Counterparty: HasChainTypes,
{
    type ClientId: Async;

    type ConnectionId: Async;

    type ChannelId: Async;

    type PortId: Async;

    type Sequence: Async;

    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height>;
}
