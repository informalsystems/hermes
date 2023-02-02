use alloc::sync::Arc;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::traits::types::height::HasHeightType;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::base::chain::traits::types::message::HasMessageType;
use crate::base::chain::traits::types::packet::HasIbcPacketTypes;
use crate::base::chain::traits::types::timestamp::HasTimestampType;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::subscription::Subscription;
use crate::std_prelude::*;

pub type Runtime<Chain> = <Chain as HasRuntime>::Runtime;

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
