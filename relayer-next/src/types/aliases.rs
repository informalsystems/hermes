use crate::traits::chain_types::{ChainTypes, IbcChainTypes};
use crate::traits::relay_types::RelayTypes;

pub type ChannelId<Chain, Counterparty> = <Chain as IbcChainTypes<Counterparty>>::ChannelId;

pub type PortId<Chain, Counterparty> = <Chain as IbcChainTypes<Counterparty>>::PortId;

pub type Sequence<Chain, Counterparty> = <Chain as IbcChainTypes<Counterparty>>::Sequence;

pub type IbcMessage<Chain, Counterparty> = <Chain as IbcChainTypes<Counterparty>>::IbcMessage;

pub type Message<Chain> = <Chain as ChainTypes>::Message;

pub type IbcEvent<Chain, Counterparty> = <Chain as IbcChainTypes<Counterparty>>::IbcEvent;

pub type Event<Chain> = <Chain as ChainTypes>::Event;

pub type Height<Chain> = <Chain as ChainTypes>::Height;

pub type Timestamp<Chain> = <Chain as ChainTypes>::Timestamp;

pub type SrcChain<Context> = <Context as RelayTypes>::SrcChain;

pub type DstChain<Context> = <Context as RelayTypes>::DstChain;

pub type Packet<Context> = <Context as RelayTypes>::Packet;
