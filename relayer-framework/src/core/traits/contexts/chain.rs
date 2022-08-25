//! The base chain contexts upon which higher level chain
//! contexts such as [`OfaChain`] are composed from.
//! 
//! These traits can be implemented over the default 
//! `OfaChain` trait if the default behavior is not 
//! suitable.

use crate::core::traits::contexts::runtime::HasRuntime;
use crate::core::traits::core::Async;
use crate::core::traits::message::{IbcMessage, Message};

/// The minimal datatypes that any chain needs to expose.
pub trait ChainContext: HasRuntime {
    type Height: Async;

    type Timestamp: Async;

    type Message: Message;

    type Event: Async;
}

/// The datatypes that IBC chains need to expose in addition
/// to the datatypes exposed by the base [`ChainContext`].
///
/// Each [`IbcChainContext`] is parameterized by a [`Counterparty`] 
/// chain.
pub trait IbcChainContext<Counterparty>: ChainContext
where
    Counterparty: ChainContext,
{
    type ClientId: Async;

    type ConnectionId: Async;

    type ChannelId: Async;

    type PortId: Async;

    type Sequence: Async;

    type IbcMessage: IbcMessage<Counterparty>;

    type IbcEvent: Async;
}
