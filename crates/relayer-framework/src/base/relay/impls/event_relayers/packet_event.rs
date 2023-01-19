use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::{HasSendPacketEvent, HasWriteAcknowledgementEvent};
use crate::base::chain::types::aliases::{Event, Height};
use crate::base::relay::traits::event_relayer::EventRelayer;
use crate::base::relay::traits::packet_relayer::CanRelayPacket;
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
{
    async fn relay_chain_event(
        relayer: &Relay,
        _height: &Height<Relay::SrcChain>,
        event: &Event<Relay::SrcChain>,
    ) -> Result<(), Relay::Error> {
        if let Some(send_packet_event) = Relay::SrcChain::try_extract_send_packet_event(event) {
            let packet = Relay::SrcChain::extract_packet_from_send_packet_event(&send_packet_event);

            relayer.relay_packet(&packet).await?;
        }

        Ok(())
    }
}

#[async_trait]
impl<Relay> EventRelayer<Relay, DestinationTarget> for PacketEventRelayer
where
    Relay: CanRelayPacket,
    Relay::SrcChain: HasWriteAcknowledgementEvent<Relay::DstChain>,
{
    async fn relay_chain_event(
        _relayer: &Relay,
        _height: &Height<Relay::DstChain>,
        _event: &Event<Relay::DstChain>,
    ) -> Result<(), Relay::Error> {
        // TODO: implementing the logic for extracting write acknowledgement
        // and relaying Ack packets.

        Ok(())
    }
}
