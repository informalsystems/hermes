use crate::base::chain::traits::context::{ChainContext, IbcChainContext};
use crate::base::chain::traits::ibc_event::HasIbcEvents;

pub type ClientId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::ClientId;

pub type ConnectionId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::ConnectionId;

pub type ChannelId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::ChannelId;

pub type PortId<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::PortId;

pub type Sequence<Chain, Counterparty> = <Chain as IbcChainContext<Counterparty>>::Sequence;

pub type Message<Chain> = <Chain as ChainContext>::Message;

pub type Event<Chain> = <Chain as ChainContext>::Event;

pub type Height<Chain> = <Chain as ChainContext>::Height;

pub type Timestamp<Chain> = <Chain as ChainContext>::Timestamp;

pub type WriteAcknowledgementEvent<Chain, Counterparty> =
    <Chain as HasIbcEvents<Counterparty>>::WriteAcknowledgementEvent;
