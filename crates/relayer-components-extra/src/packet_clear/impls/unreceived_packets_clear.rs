use async_trait::async_trait;
use ibc_relayer_components::chain::traits::queries::packet_commitments::CanQueryPacketCommitments;
use ibc_relayer_components::chain::traits::queries::unreceived_packets::{
    CanQueryUnreceivedPacketSequences, CanQueryUnreceivedPackets,
};
use ibc_relayer_components::chain::types::aliases::{ChannelId, PortId};
use ibc_relayer_components::relay::traits::packet::HasRelayPacket;
use ibc_relayer_components::relay::traits::packet_relayer::CanRelayPacket;

use crate::packet_clear::traits::packet_clear::PacketClearer;
use crate::std_prelude::*;

pub struct PacketClearRelayer;

#[async_trait]
impl<Relay> PacketClearer<Relay> for PacketClearRelayer
where
    Relay: HasRelayPacket + CanRelayPacket,
    Relay::DstChain: CanQueryPacketCommitments<Relay::SrcChain>,
    Relay::SrcChain: CanQueryUnreceivedPacketSequences<Relay::DstChain>
        + CanQueryUnreceivedPackets<Relay::DstChain>,
{
    async fn clear_receive_packets(
        relay: &Relay,
        dst_channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
        src_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
    ) -> Result<(), Relay::Error> {
        let dst_chain = relay.dst_chain();
        let src_chain = relay.src_chain();

        let commitment_sequences = dst_chain
            .query_packet_commitments(dst_channel_id, dst_port_id)
            .await
            .map_err(Relay::dst_chain_error)?;

        let (unreceived_sequences, unreceived_height) = src_chain
            .query_unreceived_packet_sequences(src_channel_id, src_port_id, &commitment_sequences)
            .await
            .map_err(Relay::src_chain_error)?;

        let unreceived_packets = src_chain
            .query_unreceived_packets(
                src_channel_id,
                src_port_id,
                dst_channel_id,
                dst_port_id,
                &unreceived_sequences,
                &unreceived_height,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        for packet in unreceived_packets.iter() {
            relay.relay_packet(packet).await?;
        }
        Ok(())
    }
}
