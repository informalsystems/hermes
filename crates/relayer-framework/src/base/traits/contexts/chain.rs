//! The base chain contexts upon which higher level chain contexts such as
//! [`OfaChain`] are composed from.
//!
//! These traits can be implemented over the default `OfaChain` trait if the
//! behavior exposed by that trait and the `AfoChain` trait are not desired.

use crate::base::traits::contexts::runtime::HasRuntime;
use crate::base::traits::core::Async;

/// The minimal datatypes that any chain needs to expose.
pub trait ChainContext: HasRuntime {
    type Height: Async;

    type Timestamp: Async;

    type Message: Async;

    type RawMessage: Async;

    type Signer: Async;

    type Event: Async;

    fn encode_message(
        message: &Self::Message,
        signer: &Self::Signer,
    ) -> Result<Self::RawMessage, Self::Error>;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error>;
}

/// The datatypes that IBC chains need to expose in addition to the datatypes
/// exposed by the base [`ChainContext`].
///
/// Each [`IbcChainContext`] is parameterized by a [`Counterparty`] chain
/// which must also implement the `ChainContext` trait.
pub trait IbcChainContext<Counterparty>: ChainContext
where
    Counterparty: ChainContext,
{
    type ClientId: Async;

    type ConnectionId: Async;

    type ChannelId: Async;

    type PortId: Async;

    type Sequence: Async;

    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height>;
}
