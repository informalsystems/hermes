use crate::traits::core::{Async, ErrorContext};
use crate::traits::message::{IbcMessage, Message};

pub trait ChainContext: ErrorContext {
    type Height: Async;

    type Timestamp: Async;

    type Message: Async + Message;

    type Event: Async;
}

pub trait IbcChainContext<Counterparty>: ChainContext
where
    Counterparty: ChainContext,
{
    type ClientId: Async;

    type ConnectionId: Async;

    type ChannelId: Async;

    type PortId: Async;

    type Sequence: Async;

    type IbcMessage: Async + IbcMessage<Counterparty>;

    type IbcEvent: Async;
}
