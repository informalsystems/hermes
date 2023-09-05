use async_trait::async_trait;

use crate::chain::traits::components::chain_status_querier::CanQueryChainStatus;
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::traits::types::status::HasChainStatusType;
use crate::relay::traits::components::packet_relayer::PacketRelayer;
use crate::relay::traits::components::packet_relayers::ack_packet::CanRelayAckPacket;
use crate::relay::traits::components::packet_relayers::receive_packet::CanRelayReceivePacket;
use crate::relay::traits::components::packet_relayers::timeout_unordered_packet::CanRelayTimeoutUnorderedPacket;
use crate::relay::traits::logs::logger::CanLogRelay;
use crate::relay::traits::logs::packet::CanLogRelayPacket;
use crate::relay::traits::packet::HasRelayPacketFields;
use crate::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FullCycleRelayer;

#[async_trait]
impl<Relay> PacketRelayer<Relay> for FullCycleRelayer
where
    Relay: CanLogRelay
        + CanLogRelayPacket
        + CanRelayAckPacket
        + CanRelayReceivePacket
        + CanRelayTimeoutUnorderedPacket
        + HasRelayPacketFields,
    Relay::SrcChain: CanQueryChainStatus,
    Relay::DstChain: CanQueryChainStatus + HasWriteAcknowledgementEvent<Relay::SrcChain>,
{
    async fn relay_packet(relay: &Relay, packet: &Packet<Relay>) -> Result<(), Relay::Error> {
        let destination_status = relay
            .dst_chain()
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
            relay.log_relay(
                Default::default(),
                "relaying timeout unordered packet",
                |log| {
                    log.field("packet", Relay::log_packet(packet));
                },
            );

            relay
                .relay_timeout_unordered_packet(destination_height, packet)
                .await?;
        } else {
            let src_chain_status = relay
                .src_chain()
                .query_chain_status()
                .await
                .map_err(Relay::src_chain_error)?;

            relay.log_relay(Default::default(), "relaying receive packet", |log| {
                log.field("packet", Relay::log_packet(packet));
            });

            let write_ack = relay
                .relay_receive_packet(
                    Relay::SrcChain::chain_status_height(&src_chain_status),
                    packet,
                )
                .await?;

            let destination_status = relay
                .dst_chain()
                .query_chain_status()
                .await
                .map_err(Relay::dst_chain_error)?;

            let destination_height = Relay::DstChain::chain_status_height(&destination_status);

            if let Some(ack) = write_ack {
                relay.log_relay(Default::default(), "relaying ack packet", |log| {
                    log.field("packet", Relay::log_packet(packet));
                });

                relay
                    .relay_ack_packet(destination_height, packet, &ack)
                    .await?;
            } else {
                relay.log_relay(
                    Default::default(),
                    "skip relaying ack packet due to lack of ack event",
                    |log| {
                        log.field("packet", Relay::log_packet(packet));
                    },
                );
            }
        }

        Ok(())
    }
}
