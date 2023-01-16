use async_trait::async_trait;
use futures::stream::StreamExt;

use crate::base::chain::traits::ibc_event::HasSendPacketEvent;
use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::types::aliases::{Event, EventSubscription, Height, Runtime};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::packet_relayer::CanRelayPacket;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::target::SourceTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::subscription::{CanSubscribe, HasSubscriptionType};
use crate::std_prelude::*;

use super::target::DestinationTarget;

#[async_trait]
pub trait EventRelayer<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventType,
{
    async fn relay_chain_event(
        relay: &Relay,
        height: &Height<Target::TargetChain>,
        event: &Event<Target::TargetChain>,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait CanRelayEvent<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasEventType,
{
    async fn relay_chain_event(
        &self,
        height: &Height<Target::TargetChain>,
        event: &Event<Target::TargetChain>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait EventSubscriptionRelayer<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime,
    Runtime<Target::TargetChain>: HasSubscriptionType,
{
    async fn relay_chain_event_subscription(
        relayer: &Relay,
        event_subscription: EventSubscription<Target::TargetChain>,
    ) -> Result<(), Relay::Error>;
}

struct BaseEventRelayer;

#[async_trait]
impl<Relay> EventRelayer<Relay, SourceTarget> for BaseEventRelayer
where
    Relay: CanRelayPacket,
    Relay::SrcChain: HasSendPacketEvent<Relay::DstChain>,
{
    async fn relay_chain_event(
        relayer: &Relay,
        _height: &Height<Relay::SrcChain>,
        event: &<Relay::SrcChain as HasEventType>::Event,
    ) -> Result<(), Relay::Error> {
        if let Some(send_packet_event) = Relay::SrcChain::try_extract_send_packet_event(event) {
            let packet = Relay::SrcChain::extract_packet_from_send_packet_event(&send_packet_event);

            relayer.relay_packet(&packet).await?;
        }

        Ok(())
    }
}

#[async_trait]
impl<Relay> EventRelayer<Relay, DestinationTarget> for BaseEventRelayer
where
    Relay: CanRelayPacket,
    Relay::SrcChain: HasSendPacketEvent<Relay::DstChain>,
{
    async fn relay_chain_event(
        _relayer: &Relay,
        _height: &Height<Relay::DstChain>,
        _event: &Event<Relay::DstChain>,
    ) -> Result<(), Relay::Error> {
        Ok(())
    }
}

struct SequentialSendPacketEventRelayer;

#[async_trait]
impl<Relay, Target, Runtime> EventSubscriptionRelayer<Relay, Target>
    for SequentialSendPacketEventRelayer
where
    Relay: CanRelayEvent<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanSubscribe,
{
    async fn relay_chain_event_subscription(
        relay: &Relay,
        event_subscription: EventSubscription<Target::TargetChain>,
    ) -> Result<(), Relay::Error> {
        loop {
            let event_stream = Runtime::subscribe(&event_subscription);

            event_stream
                .for_each(|(height, event)| async move {
                    let _ = relay.relay_chain_event(&height, &event).await;
                })
                .await;
        }
    }
}
