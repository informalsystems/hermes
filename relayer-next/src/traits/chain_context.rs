use core::fmt::{Debug, Display};

use super::message::IbcMessage as SomeIbcMessage;

pub type ChannelId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::ChannelId;
pub type PortId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::PortId;
pub type Sequence<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::Sequence;
pub type IbcMessage<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::IbcMessage;
pub type IbcEvent<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::IbcEvent;

pub type Height<Chain> = <Chain as ChainContext>::Height;
pub type Timestamp<Chain> = <Chain as ChainContext>::Timestamp;

pub trait ChainContext: Sized + Send + Sync + 'static {
    type Error;

    type Height: Clone + Debug;
    type Timestamp: Clone + Debug;

    type Address: Clone + Display;
}

pub trait IbcChainContext<Counterparty: ChainContext>: ChainContext {
    type ChannelId: Clone + Debug;
    type PortId: Clone + Debug;
    type Sequence: Clone + Debug;

    type IbcMessage: SomeIbcMessage<Counterparty>;
    type IbcEvent;
}
