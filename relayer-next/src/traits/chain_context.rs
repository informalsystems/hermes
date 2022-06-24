use super::message::{IbcMessage as SomeIbcMessage, Message as SomeMessage};

pub trait ChainContext: Sized + Send + Sync + 'static {
    type Error;

    type Height;
    type Timestamp;

    type Message: SomeMessage;
}

pub trait IbcChainContext<Counterparty>: ChainContext
where
    Counterparty: ChainContext,
{
    type ChannelId;
    type PortId;
    type Sequence;

    type IbcMessage: SomeIbcMessage<Counterparty>;
    type IbcEvent;
}
