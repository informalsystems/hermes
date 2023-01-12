use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasSendPacketEvent;
use crate::base::chain::traits::types::event::HasEventType;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::packet_relayer::CanRelayPacket;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::target::SourceTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::subscription::{CanSubscribe, HasSubscriptionType};
use crate::std_prelude::*;

#[async_trait]
pub trait EventRelayer<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventType,
{
    async fn relay_chain_event(
        relayer: &Relay,
        event: &<Target::TargetChain as HasEventType>::Event,
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
        event: &<Target::TargetChain as HasEventType>::Event,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait EventStreamRelayer<Relay, Target>: Async
where
    Relay: HasRelayTypes + HasRuntime,
    Relay::Runtime: HasSubscriptionType,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventType,
{
    async fn relay_chain_event_stream(
        relayer: &Relay,
        event_subscription: &<Target::TargetChain as HasEventType>::Event,
    ) -> Result<(), Relay::Error>;
}

struct SequentialSendPacketEventRelayer;

#[async_trait]
impl<Relay> EventRelayer<Relay, SourceTarget> for SequentialSendPacketEventRelayer
where
    Relay: CanRelayPacket,
    Relay::SrcChain: HasSendPacketEvent<Relay::DstChain>,
{
    async fn relay_chain_event(
        relayer: &Relay,
        event: &<Relay::SrcChain as HasEventType>::Event,
    ) -> Result<(), Relay::Error> {
        if let Some(send_packet_event) = Relay::SrcChain::try_extract_send_packet_event(event) {
            let packet = Relay::SrcChain::extract_packet_from_send_packet_event(&send_packet_event);

            relayer.relay_packet(&packet).await?;
        }

        Ok(())
    }
}
