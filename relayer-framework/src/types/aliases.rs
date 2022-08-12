use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::contexts::ibc_event::IbcEventContext;
use crate::traits::contexts::relay::RelayContext;

pub type ClientId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::ClientId;

pub type ConnectionId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::ConnectionId;

pub type ChannelId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::ChannelId;

pub type PortId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::PortId;

pub type Sequence<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::Sequence;

pub type IbcMessage<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::IbcMessage;

pub type Message<Chain> = <Chain as ChainContext>::Message;

pub type IbcEvent<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::IbcEvent;

pub type Event<Chain> = <Chain as ChainContext>::Event;

pub type Height<Chain> = <Chain as ChainContext>::Height;

pub type Timestamp<Chain> = <Chain as ChainContext>::Timestamp;

pub type SrcChain<Context> = <Context as RelayContext>::SrcChain;

pub type DstChain<Context> = <Context as RelayContext>::DstChain;

pub type Packet<Context> = <Context as RelayContext>::Packet;

pub type WriteAcknowledgementEvent<Chain, Counterparty> =
    <Chain as IbcEventContext<Counterparty>>::WriteAcknowledgementEvent;
