use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::queries::status::{CanQueryChainStatus, HasChainStatus};
use crate::base::relay::traits::packet_relayer::PacketRelayer;
use crate::base::relay::traits::packet_relayers::ack_packet::HasAckPacketRelayer;
use crate::base::relay::traits::packet_relayers::receive_packet::CanRelayReceivePacket;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FullRelayer;

#[async_trait]
impl<Relay> PacketRelayer<Relay> for FullRelayer
where
    Relay: HasRelayTypes,
    Relay: HasAckPacketRelayer,
    Relay: CanRelayReceivePacket,
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
    Relay::SrcChain: CanQueryChainStatus,
    Relay::DstChain: CanQueryChainStatus,
{
    async fn relay_packet(relay: &Relay, packet: &Packet<Relay>) -> Result<(), Relay::Error> {
        let source_status = relay.source_chain().query_chain_status().await?;

        let write_ack = relay
            .relay_receive_packet(Relay::SrcChain::chain_status_height(&source_status), packet)
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
