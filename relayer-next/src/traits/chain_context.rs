use crate::traits::core::CoreTraits;
use crate::traits::message::{IbcMessage as SomeIbcMessage, Message as SomeMessage};

pub trait ChainContext: CoreTraits {
    type Error: CoreTraits;

    type Height: CoreTraits;
    type Timestamp: CoreTraits;

    type Message: CoreTraits + SomeMessage;
}

pub trait IbcChainContext<Counterparty>: ChainContext
where
    Counterparty: ChainContext,
{
    type ChannelId: CoreTraits;
    type PortId: CoreTraits;
    type Sequence: CoreTraits;

    type IbcMessage: CoreTraits + SomeIbcMessage<Counterparty>;
    type IbcEvent: CoreTraits;
}
