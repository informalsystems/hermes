use alloc::sync::Arc;
use core::pin::Pin;
use futures::stream::Stream;

use crate::chain::traits::types::event::HasEventType;
use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::traits::types::message::HasMessageType;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::chain::traits::types::timestamp::HasTimestampType;
use crate::runtime::traits::subscription::Subscription;
use crate::std_prelude::*;

pub type IncomingPacket<Chain, Counterparty> =
    <Chain as HasIbcPacketTypes<Counterparty>>::IncomingPacket;

pub type OutgoingPacket<Chain, Counterparty> =
    <Chain as HasIbcPacketTypes<Counterparty>>::OutgoingPacket;

pub type ClientId<Chain, Counterparty> = <Chain as HasIbcChainTypes<Counterparty>>::ClientId;

pub type ConnectionId<Chain, Counterparty> =
    <Chain as HasIbcChainTypes<Counterparty>>::ConnectionId;

pub type ChannelId<Chain, Counterparty> = <Chain as HasIbcChainTypes<Counterparty>>::ChannelId;

pub type PortId<Chain, Counterparty> = <Chain as HasIbcChainTypes<Counterparty>>::PortId;

pub type Sequence<Chain, Counterparty> = <Chain as HasIbcChainTypes<Counterparty>>::Sequence;

pub type Message<Chain> = <Chain as HasMessageType>::Message;

pub type Event<Chain> = <Chain as HasEventType>::Event;

pub type Height<Chain> = <Chain as HasHeightType>::Height;

pub type Timestamp<Chain> = <Chain as HasTimestampType>::Timestamp;

pub type WriteAcknowledgementEvent<Chain, Counterparty> =
    <Chain as HasWriteAcknowledgementEvent<Counterparty>>::WriteAcknowledgementEvent;

pub type EventStream<Chain> =
    Pin<Box<dyn Stream<Item = Arc<(Height<Chain>, Event<Chain>)>> + Send + 'static>>;

pub type EventSubscription<Chain> = Arc<dyn Subscription<Item = (Height<Chain>, Event<Chain>)>>;
