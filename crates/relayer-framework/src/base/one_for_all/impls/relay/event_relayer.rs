use async_trait::async_trait;

use crate::base::chain::types::aliases::{Event, Height};
use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayPreset};
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::impls::event_relayers::packet_event::PacketEventRelayer;
use crate::base::relay::traits::event_relayer::{CanRelayEvent, EventRelayer};
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Preset> CanRelayEvent<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaRelayPreset<Relay>,
{
    async fn relay_chain_event(
        &self,
        height: &Height<Self::SrcChain>,
        event: &Event<Self::SrcChain>,
    ) -> Result<(), Relay::Error> {
        <PacketEventRelayer as EventRelayer<Self, SourceTarget>>::relay_chain_event(
            self, height, event,
        )
        .await
    }
}

#[async_trait]
impl<Relay, Preset> CanRelayEvent<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaRelayPreset<Relay>,
{
    async fn relay_chain_event(
        &self,
        height: &Height<Self::DstChain>,
        event: &Event<Self::DstChain>,
    ) -> Result<(), Relay::Error> {
        <PacketEventRelayer as EventRelayer<Self, DestinationTarget>>::relay_chain_event(
            self, height, event,
        )
        .await
    }
}
