use async_trait::async_trait;

use crate::chain::traits::types::ibc_events::send_packet::HasSendPacketEvent;
use crate::chain::traits::types::ibc_events::write_ack::{
    CanBuildPacketFromWriteAckEvent, HasWriteAcknowledgementEvent,
};
use crate::chain::types::aliases::{Event, Height};
use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::impls::packet_filters::chain::{
    MatchPacketDestinationChain, MatchPacketSourceChain,
};
use crate::relay::traits::event_relayer::EventRelayer;
use crate::relay::traits::logs::logger::CanLogRelay;
use crate::relay::traits::logs::packet::CanLogRelayPacket;
use crate::relay::traits::packet_filter::{CanFilterPackets, PacketFilter};
use crate::relay::traits::packet_relayer::CanRelayPacket;
use crate::relay::traits::packet_relayers::ack_packet::CanRelayAckPacket;
use crate::relay::traits::packet_relayers::lock::HasPacketLock;
use crate::relay::traits::target::{DestinationTarget, SourceTarget};
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
    Relay: CanRelayAckPacket + CanFilterPackets + HasPacketLock + CanLogRelay + CanLogRelayPacket,
    Relay::DstChain: CanBuildPacketFromWriteAckEvent<Relay::SrcChain>,
    MatchPacketSourceChain: PacketFilter<Relay>,
{
    async fn relay_chain_event(
        relay: &Relay,
        height: &Height<Relay::DstChain>,
        event: &Event<Relay::DstChain>,
    ) -> Result<(), Relay::Error> {
        let m_ack_event = Relay::DstChain::try_extract_write_acknowledgement_event(event);

        if let Some(ack_event) = m_ack_event {
            let packet = Relay::DstChain::build_packet_from_write_acknowledgement_event(&ack_event);

            /*
               First check whether the packet is targetted for the destination chain,
               then use the packet filter in the relay context, as we skip `CanRelayPacket`
               which would have done the packet filtering.
            */
            if MatchPacketSourceChain::should_relay_packet(relay, packet).await?
                && relay.should_relay_packet(packet).await?
            {
                let m_lock = relay.try_acquire_packet_lock(packet).await;

                /*
                   Only relay the ack packet if there isn't another packet relayer
                   trying to relay the same packet. This may happen because packet
                   relayers like `FullCycleRelayer` also relay the ack packet right
                   after it relays the recv packet.

                   On the other hand, this event relayer relays based on the ack
                   event that is fired, which is independent of the main packet
                   relayer. Hence it has to use the packet lock to synchronize
                   with the other packet worker.

                   Note that it is still necessary to handle event-based ack
                   relaying here, as we cannot just rely on the main packet
                   worker to relay the ack packet. It is also possible that the
                   relayer missed the send packet event, which gets relayed by
                   another relayer. In that case, we can still relay the ack
                   packet here based on the ack event.
                */
                match m_lock {
                    Some(_lock) => {
                        relay.relay_ack_packet(height, packet, &ack_event).await?;
                    }
                    None => {
                        relay.log_relay(
                            Relay::Logger::LEVEL_TRACE,
                            "skip relaying ack packet, as another packet relayer has acquired the packet lock",
                            |log| {
                                log.field("packet", Relay::log_packet(packet));
                            },
                        );
                    }
                }
            }
        }

        Ok(())
    }
}
