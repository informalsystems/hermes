use async_trait::async_trait;

use crate::base::chain::traits::types::ibc_events::send_packet::HasSendPacketEvent;
use crate::base::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::base::chain::types::aliases::{Event, Height};
use crate::base::relay::impls::packet_filters::chain::{
    MatchPacketDestinationChain, MatchPacketSourceChain,
};
use crate::base::relay::traits::event_relayer::EventRelayer;
use crate::base::relay::traits::packet_filter::{CanFilterPackets, PacketFilter};
use crate::base::relay::traits::packet_relayer::CanRelayPacket;
use crate::base::relay::traits::packet_relayers::ack_packet::CanRelayAckPacket;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

/**
   A packet event relayer that performs packet relaying based on chain events
   related to IBC packets.

   The implementation of `PacketEventRelayer` for the [`SourceTarget`] is
   different from the [`DestinationTarget`]. This is because the packet
   relaying operations from the source chain is different from the target chain.

   When relaying events from the source chain, the packet event relayer is
   mostly interested in the `SendPacket` event, so that it can relay a
   `RecvPacket` message to the destination chain, or a `TimeoutPacket` message
   to the source chain.

   When relaying events from the destination chain, the packet event relayer
   is mostly interested in the `WriteAcknowledgement` event, so that it can
   relay a `AckPacket` message to the source chain.
*/
pub struct PacketEventRelayer;

#[async_trait]
impl<Relay> EventRelayer<Relay, SourceTarget> for PacketEventRelayer
where
    Relay: CanRelayPacket,
    Relay::SrcChain: HasSendPacketEvent<Relay::DstChain>,
    MatchPacketDestinationChain: PacketFilter<Relay>,
{
    async fn relay_chain_event(
        relay: &Relay,
        _height: &Height<Relay::SrcChain>,
        event: &Event<Relay::SrcChain>,
    ) -> Result<(), Relay::Error> {
        if let Some(send_packet_event) = Relay::SrcChain::try_extract_send_packet_event(event) {
            let packet = Relay::SrcChain::extract_packet_from_send_packet_event(&send_packet_event);

            if MatchPacketDestinationChain::should_relay_packet(relay, &packet).await? {
                relay.relay_packet(&packet).await?;
            }
        }

        Ok(())
    }
}

#[async_trait]
impl<Relay> EventRelayer<Relay, DestinationTarget> for PacketEventRelayer
where
    Relay: CanRelayAckPacket + CanFilterPackets,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
    MatchPacketSourceChain: PacketFilter<Relay>,
{
    async fn relay_chain_event(
        relay: &Relay,
        height: &Height<Relay::DstChain>,
        event: &Event<Relay::DstChain>,
    ) -> Result<(), Relay::Error> {
        let m_ack_event = Relay::DstChain::try_extract_write_acknowledgement_event(event);

        if let Some(ack_event) = m_ack_event {
            let packet =
                Relay::DstChain::extract_packet_from_write_acknowledgement_event(&ack_event);

            // First check whether the packet is targetted for the destination chain,
            // then use the packet filter in the relay context, as we skip `CanRelayPacket`
            // which would have done the packet filtering.
            if MatchPacketSourceChain::should_relay_packet(relay, packet).await?
                && relay.should_relay_packet(packet).await?
            {
                // TODO: Add a middleware for Ack relayer so that it does not
                // relay ack twice. (another time inside `FullCycleRelayer`)
                relay.relay_ack_packet(height, packet, &ack_event).await?;
            }
        }

        // TODO: implementing the logic for extracting write acknowledgement
        // and relaying Ack packets.

        Ok(())
    }
}
