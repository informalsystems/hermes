use async_trait::async_trait;

use crate::base::traits::contexts::ibc_event::HasIbcEvents;
use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::packet_relayer::PacketRelayer;
use crate::base::traits::packet_relayers::ack_packet::HasAckPacketRelayer;
use crate::base::traits::packet_relayers::receive_packet::HasReceivePacketRelayer;
use crate::base::traits::queries::status::{HasChainStatus, HasChainStatusQuerier};
use crate::base::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FullRelayer;

#[async_trait]
impl<Relay> PacketRelayer<Relay> for FullRelayer
where
    Relay: RelayContext,
    Relay: HasAckPacketRelayer,
    Relay: HasReceivePacketRelayer,
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
    Relay::SrcChain: HasChainStatusQuerier,
    Relay::DstChain: HasChainStatusQuerier,
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
