use async_trait::async_trait;
use futures_util::{stream, StreamExt};
use ibc_relayer_components::chain::traits::queries::packet_commitments::CanQueryPacketCommitments;
use ibc_relayer_components::chain::traits::queries::unreceived_packets::CanQueryUnreceivedPackets;
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
    Relay::SrcChain: CanQueryUnreceivedPackets<Relay::DstChain>,
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

        let unreceived_packets = src_chain
            .query_unreceived_packets(
                src_channel_id,
                src_port_id,
                dst_channel_id,
                dst_port_id,
                &commitment_sequences,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        stream::iter(unreceived_packets)
            .for_each_concurrent(None, |t| async move {
                // Ignore any relaying errors, as the relayer still needs to proceed
                // relaying the next event regardless.
                let _ = relay.relay_packet(&t).await;
            })
            .await;

        Ok(())
    }
}
