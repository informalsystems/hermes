use crate::traits::core::{Async, ErrorContext};
use crate::traits::message::{IbcMessage, Message};

pub trait ChainTypes: ErrorContext {
    type Height: Async;
    type Timestamp: Async;

    type Message: Async + Message;
    type Event: Async;
}

pub trait IbcChainTypes<Counterparty: ChainTypes>:
    ChainTypes<Message = Self::IbcMessage, Event = Self::IbcEvent>
{
    type ChannelId: Async;
    type PortId: Async;
    type Sequence: Async;

    type IbcMessage: Async + IbcMessage<Counterparty>;
    type IbcEvent: Async;
}

pub trait ChainContext: ErrorContext {
    type ChainTypes: ChainTypes;
}

pub trait IbcChainContext<Counterparty: ChainTypes>:
    ChainContext<ChainTypes = Self::IbcChainTypes>
{
    type IbcChainTypes: IbcChainTypes<Counterparty>;
}
