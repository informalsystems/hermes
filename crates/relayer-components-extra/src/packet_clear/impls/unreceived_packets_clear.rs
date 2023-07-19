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
    async fn clear_packets(
        relay: &Relay,
        channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
        counterparty_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        counterparty_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
    ) -> Result<(), Relay::Error> {
        let chain = relay.dst_chain();
        let counterparty_chain = relay.src_chain();

        let commitment_sequences = chain
            .query_packet_commitments(channel_id, port_id)
            .await
            .map_err(Relay::dst_chain_error)?;

        let (unreceived_sequences, unreceived_height) = counterparty_chain
            .query_unreceived_packet_sequences(
                counterparty_channel_id,
                counterparty_port_id,
                &commitment_sequences,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        let unreceived_packets = counterparty_chain
            .query_unreceived_packets(
                counterparty_channel_id,
                counterparty_port_id,
                channel_id,
                port_id,
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
