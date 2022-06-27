use crate::traits::core::{Async, ErrorContext};
use crate::traits::message::{IbcMessage as SomeIbcMessage, Message as SomeMessage};

pub trait ChainTypes: ErrorContext {
    type Height: Async;
    type Timestamp: Async;

    type Message: Async + SomeMessage;
}

pub trait IbcChainTypes<Counterparty: ChainTypes>: ChainTypes {
    type ChannelId: Async;
    type PortId: Async;
    type Sequence: Async;

    type IbcMessage: Async + SomeIbcMessage<Counterparty>;
    type IbcEvent: Async;
}

pub trait IbcChainContext<Counterparty: ChainTypes>: ErrorContext {
    type IbcChainTypes: IbcChainTypes<Counterparty>;
}
