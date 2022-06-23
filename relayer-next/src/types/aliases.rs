use crate::traits::chain_context::{ChainContext, IbcChainContext};

pub type ChannelId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::ChannelId;

pub type PortId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::PortId;

pub type Sequence<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::Sequence;

pub type IbcMessage<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::IbcMessage;

pub type IbcEvent<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::IbcEvent;

pub type Height<Chain> = <Chain as ChainContext>::Height;

pub type Timestamp<Chain> = <Chain as ChainContext>::Timestamp;
