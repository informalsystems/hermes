use async_trait::async_trait;

use crate::chain::traits::queries::channel::CanQueryCounterpartyChainIdFromChannel;
use crate::chain::traits::types::chain_id::HasChainId;
use crate::relay::traits::components::packet_filter::PacketFilter;
use crate::relay::traits::packet::HasRelayPacketFields;
use crate::std_prelude::*;

pub struct MatchPacketSourceChain;

pub struct MatchPacketDestinationChain;

#[async_trait]
impl<Relay> PacketFilter<Relay> for MatchPacketSourceChain
where
    Relay: HasRelayPacketFields,
    Relay::DstChain: CanQueryCounterpartyChainIdFromChannel<Relay::SrcChain>,
    Relay::SrcChain: HasChainId,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        let dst_channel_id = Relay::packet_dst_channel_id(packet);
        let dst_port = Relay::packet_dst_port(packet);

        let src_chain_id = relay
            .dst_chain()
            .query_chain_id_from_channel_id(dst_channel_id, dst_port)
            .await
            .map_err(Relay::dst_chain_error)?;

        let same_chain = &src_chain_id == relay.src_chain().chain_id();

        Ok(same_chain)
    }
}

#[async_trait]
impl<Relay> PacketFilter<Relay> for MatchPacketDestinationChain
where
    Relay: HasRelayPacketFields,
    Relay::SrcChain: CanQueryCounterpartyChainIdFromChannel<Relay::DstChain>,
    Relay::DstChain: HasChainId,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        let src_channel_id = Relay::packet_src_channel_id(packet);
        let src_port = Relay::packet_src_port(packet);

        let dst_chain_id = relay
            .src_chain()
            .query_chain_id_from_channel_id(src_channel_id, src_port)
            .await
            .map_err(Relay::src_chain_error)?;

        let same_chain = &dst_chain_id == relay.dst_chain().chain_id();

        Ok(same_chain)
    }
}
