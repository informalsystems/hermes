use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::{HasSendPacketEvent, HasWriteAcknowledgementEvent};
use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::types::aliases::{Event, Height};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::packet_relayer::CanRelayPacket;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

/**
   An event relayer performs relay actions based on one event at a time from
   the target chain.

   The event relayer is a general abstraction over other relayer types that
   need to be reactive to chain events. This includes the
   [packet relayer](CanRelayPacket), but also future relayers such as
   connection and channel handshake relayers.
*/
#[async_trait]
pub trait EventRelayer<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventType,
{
    /**
       Relay a chain event which is emitted from the target chain at a given
       height.

       The chain event could be anything. If the given event is not related to
       IBC, the relayer should do nothing and return `Ok(())`.
    */
    async fn relay_chain_event(
        relay: &Relay,
        height: &Height<Target::TargetChain>,
        event: &Event<Target::TargetChain>,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait CanRelayEvent<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasEventType,
{
    async fn relay_chain_event(
        &self,
        height: &Height<Target::TargetChain>,
        event: &Event<Target::TargetChain>,
    ) -> Result<(), Self::Error>;
}

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
struct PacketEventRelayer;

#[async_trait]
impl<Relay> EventRelayer<Relay, SourceTarget> for PacketEventRelayer
where
    Relay: CanRelayPacket,
    Relay::SrcChain: HasSendPacketEvent<Relay::DstChain>,
{
    async fn relay_chain_event(
        relayer: &Relay,
        _height: &Height<Relay::SrcChain>,
        event: &<Relay::SrcChain as HasEventType>::Event,
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
