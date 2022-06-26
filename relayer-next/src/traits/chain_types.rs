use crate::traits::core::CoreTraits;
use crate::traits::message::{IbcMessage as SomeIbcMessage, Message as SomeMessage};

pub trait ChainTypes: CoreTraits {
    type Error: CoreTraits;

    type Height: CoreTraits;
    type Timestamp: CoreTraits;

    type Message: CoreTraits + SomeMessage;
}

pub trait IbcChainTypes<Counterparty: ChainTypes>: ChainTypes {
    type ChannelId: CoreTraits;
    type PortId: CoreTraits;
    type Sequence: CoreTraits;

    type IbcMessage: CoreTraits + SomeIbcMessage<Counterparty>;
    type IbcEvent: CoreTraits;
}

pub trait IbcChainContext<Counterparty: ChainTypes>: CoreTraits {
    type Error: CoreTraits;

    type IbcChainTypes: IbcChainTypes<Counterparty>;
}
