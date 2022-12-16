use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::queries::status::{CanQueryChainStatus, HasChainStatus};
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::CanRelayAckPacket;
use crate::base::relay::traits::packet_relayers::receive_packet::CanRelayReceivePacket;
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::CanRelayTimeoutUnorderedPacket;
use crate::base::relay::traits::types::{HasRelayPacketFields, HasRelayTypes};
use crate::base::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FullCycleRelayer;

#[async_trait]
impl<Relay> PacketRelayer<Relay> for FullCycleRelayer
where
    Relay: HasRelayTypes,
    Relay: CanRelayAckPacket,
    Relay: CanRelayReceivePacket,
    Relay: CanRelayTimeoutUnorderedPacket,
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
    Relay::SrcChain: CanQueryChainStatus,
    Relay::DstChain: CanQueryChainStatus,
{
    async fn relay_packet(relay: &Relay, packet: &Packet<Relay>) -> Result<(), Relay::Error> {
        let destination_status = relay
            .destination_chain()
            .query_chain_status()
            .await
            .map_err(Relay::dst_chain_error)?;

        let destination_height = Relay::DstChain::chain_status_height(&destination_status);
        let destination_timestamp = Relay::DstChain::chain_status_timestamp(&destination_status);

        let packet_timeout_height = Relay::packet_timeout_height(packet);
        let packet_timeout_timestamp = Relay::packet_timeout_timestamp(packet);

        let has_packet_timed_out = if let Some(packet_timeout_height) = packet_timeout_height {
            destination_height > packet_timeout_height
                || destination_timestamp > packet_timeout_timestamp
        } else {
            destination_timestamp > packet_timeout_timestamp
        };

        if has_packet_timed_out {
            relay
                .relay_timeout_unordered_packet(destination_height, packet)
                .await?;
        } else {
            let source_chain_status = relay
                .source_chain()
                .query_chain_status()
                .await
                .map_err(Relay::src_chain_error)?;

            let write_ack = relay
                .relay_receive_packet(
                    Relay::SrcChain::chain_status_height(&source_chain_status),
                    packet,
                )
                .await?;

            let destination_status = relay
                .destination_chain()
                .query_chain_status()
                .await
                .map_err(Relay::dst_chain_error)?;

            let destination_height = Relay::DstChain::chain_status_height(&destination_status);

            if let Some(ack) = write_ack {
                relay
                    .relay_ack_packet(destination_height, packet, &ack)
                    .await?;
            }
        }

        Ok(())
    }
}
