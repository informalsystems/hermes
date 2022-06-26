use crate::traits::core::CoreTraits;
use crate::traits::message::{IbcMessage, Message};

pub trait ChainTypes: CoreTraits {
    type Error: CoreTraits;

    type Height: CoreTraits;

    type Timestamp: CoreTraits;

    type Message: CoreTraits + Message;
}

pub trait IbcChainTypes<Counterparty>: ChainTypes
where
    Counterparty: ChainTypes,
{
    type IbcMessage: CoreTraits + IbcMessage<Counterparty>;

    type ChannelId: CoreTraits;

    type PortId: CoreTraits;

    type Sequence: CoreTraits;

    type IbcEvent: CoreTraits;
}

pub trait IbcChainContext<Counterparty: ChainTypes>: CoreTraits {
    type Error: CoreTraits;

    type IbcChainTypes: IbcChainTypes<Counterparty>;
}
