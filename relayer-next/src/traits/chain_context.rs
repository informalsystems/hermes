use core::fmt::Debug;

use super::message::{IbcMessage as SomeIbcMessage, Message as SomeMessage};

pub trait ChainContext: Sized + Send + Sync + 'static {
    type Error;

    type Height: Clone + Debug;
    type Timestamp: Clone + Debug;

    type Message: SomeMessage;
}

pub trait IbcChainContext<Counterparty: ChainContext>: ChainContext {
    type ChannelId: Clone + Debug;
    type PortId: Clone + Debug;
    type Sequence: Clone + Debug;

    type IbcMessage: SomeIbcMessage<Counterparty>;
    type IbcEvent;
}
