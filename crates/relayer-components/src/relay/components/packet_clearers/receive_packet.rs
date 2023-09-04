use async_trait::async_trait;
use futures_util::stream;
use futures_util::StreamExt;

use crate::chain::traits::queries::packet_commitments::CanQueryPacketCommitments;
use crate::chain::traits::queries::send_packet::CanQuerySendPacketsFromSequences;
use crate::chain::traits::queries::unreceived_packets::CanQueryUnreceivedPacketSequences;
use crate::chain::types::aliases::{ChannelId, PortId};
use crate::relay::traits::components::packet_clearer::PacketClearer;
use crate::relay::traits::components::packet_relayer::CanRelayPacket;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

pub struct ClearReceivePackets;

#[async_trait]
impl<Relay> PacketClearer<Relay> for ClearReceivePackets
where
    Relay: HasRelayPacket + CanRelayPacket,
    Relay::DstChain: CanQueryUnreceivedPacketSequences<Relay::SrcChain>,
    Relay::SrcChain: CanQueryPacketCommitments<Relay::DstChain>
        + CanQuerySendPacketsFromSequences<Relay::DstChain>,
{
    async fn clear_packets(
        relay: &Relay,
        src_channel_id: &ChannelId<Relay::SrcChain, Relay::DstChain>,
        src_port_id: &PortId<Relay::SrcChain, Relay::DstChain>,
        dst_channel_id: &ChannelId<Relay::DstChain, Relay::SrcChain>,
        dst_port_id: &PortId<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error> {
        let dst_chain = relay.dst_chain();
        let src_chain = relay.src_chain();

        let (commitment_sequences, height) = src_chain
            .query_packet_commitments(src_channel_id, src_port_id)
            .await
            .map_err(Relay::src_chain_error)?;

        let unreceived_sequences = dst_chain
            .query_unreceived_packet_sequences(dst_channel_id, dst_port_id, &commitment_sequences)
            .await
            .map_err(Relay::dst_chain_error)?;

        let send_packets = src_chain
            .query_send_packets_from_sequences(
                src_channel_id,
                src_port_id,
                dst_channel_id,
                dst_port_id,
                &unreceived_sequences,
                &height,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        stream::iter(send_packets)
            .for_each_concurrent(None, |t| async move {
                // Ignore any relaying errors, as the relayer still needs to proceed
                // relaying the next event regardless.
                let _ = relay.relay_packet(&t).await;
            })
            .await;

        Ok(())
    }
}
