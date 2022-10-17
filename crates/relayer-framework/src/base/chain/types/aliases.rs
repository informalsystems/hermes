use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::types::{HasChainTypes, HasIbcChainTypes};

pub type ClientId<Chain, Counterparty> = <Chain as HasIbcChainTypes<Counterparty>>::ClientId;

pub type ConnectionId<Chain, Counterparty> =
    <Chain as HasIbcChainTypes<Counterparty>>::ConnectionId;

pub type ChannelId<Chain, Counterparty> = <Chain as HasIbcChainTypes<Counterparty>>::ChannelId;

pub type PortId<Chain, Counterparty> = <Chain as HasIbcChainTypes<Counterparty>>::PortId;

pub type Sequence<Chain, Counterparty> = <Chain as HasIbcChainTypes<Counterparty>>::Sequence;

pub type Message<Chain> = <Chain as HasChainTypes>::Message;

pub type Event<Chain> = <Chain as HasChainTypes>::Event;

pub type Height<Chain> = <Chain as HasChainTypes>::Height;

pub type Timestamp<Chain> = <Chain as HasChainTypes>::Timestamp;

pub type WriteAcknowledgementEvent<Chain, Counterparty> =
    <Chain as HasIbcEvents<Counterparty>>::WriteAcknowledgementEvent;
