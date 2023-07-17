use async_trait::async_trait;

use crate::chain::traits::queries::packet_commitments::CanQueryPacketCommitments;
use crate::chain::traits::queries::unreceived_packets::CanQueryUnreceivedPacketEvents;
use crate::chain::types::aliases::{ChannelId, Height, PortId};
use crate::relay::impls::packet_filters::chain::MatchPacketDestinationChain;
use crate::relay::traits::event_relayer::CanRelayEvent;
use crate::relay::traits::packet::HasRelayPacket;
use crate::relay::traits::packet_clear::PacketClearerWithTarget;
use crate::relay::traits::packet_filter::PacketFilter;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct PacketClearRelayer;

#[async_trait]
impl<Relay, Target> PacketClearerWithTarget<Relay, Target> for PacketClearRelayer
where
    Relay: HasRelayPacket + CanRelayEvent<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: CanQueryPacketCommitments<Target::CounterpartyChain>
        + CanQueryUnreceivedPacketEvents<Target::CounterpartyChain>,
    MatchPacketDestinationChain: PacketFilter<Relay>,
{
    async fn clear_packets_with_target(
        relay: &Relay,
        channel_id: &ChannelId<Target::TargetChain, Target::CounterpartyChain>,
        port_id: &PortId<Target::TargetChain, Target::CounterpartyChain>,
        counterparty_channel_id: &ChannelId<Target::CounterpartyChain, Target::TargetChain>,
        counterparty_port_id: &PortId<Target::CounterpartyChain, Target::TargetChain>,
        height: &Height<Target::TargetChain>,
    ) -> Result<(), Relay::Error> {
        let chain = Target::target_chain(relay);

        let sequences = chain
            .query_packet_commitments(channel_id, port_id)
            .await
            .map_err(Target::target_chain_error)?;

        let unreceived_packet_events = chain
            .query_unreceived_packet_events(
                channel_id,
                port_id,
                counterparty_channel_id,
                counterparty_port_id,
                &sequences,
                height,
            )
            .await
            .map_err(Target::target_chain_error)?;

        for event in unreceived_packet_events.iter() {
            relay.relay_chain_event(height, event).await?;
        }
        Ok(())
    }
}
