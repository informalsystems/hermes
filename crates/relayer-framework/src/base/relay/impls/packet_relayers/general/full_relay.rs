use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::queries::status::{CanQueryChainStatus, HasChainStatus};
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::CanRelayAckPacket;
use crate::base::relay::traits::packet_relayers::receive_packet::CanRelayReceivePacket;
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::CanRelayTimeoutUnorderedPacket;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FullRelayer;

#[async_trait]
impl<Relay> PacketRelayer<Relay> for FullRelayer
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
        let source_chain_status = relay.source_chain().query_chain_status().await?;
        let source_chain_height = Relay::SrcChain::chain_status_height(&source_chain_status);
        let source_chain_timestamp = Relay::SrcChain::chain_status_timestamp(&source_chain_status);

        let packet_timeout_height = Relay::packet_timeout_height(&packet);
        let packet_timeout_timestamp = Relay::packet_timeout_timestamp(&packet);

        let has_packet_timed_out = false;

        let write_ack = relay
            .relay_receive_packet(
                Relay::SrcChain::chain_status_height(&source_chain_status),
                packet,
            )
            .await?;

        if let Some(ack) = write_ack {
            let destination_status = relay.destination_chain().query_chain_status().await?;

            relay
                .relay_ack_packet(
                    Relay::DstChain::chain_status_height(&destination_status),
                    packet,
                    &ack,
                )
                .await?;
        }

        Ok(())
    }
}
