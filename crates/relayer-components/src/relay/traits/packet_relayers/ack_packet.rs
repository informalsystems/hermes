use async_trait::async_trait;

use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayAckPacket: HasRelayPacket
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
    async fn relay_ack_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
        ack: &WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait AckPacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
{
    async fn relay_ack_packet(
        context: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error>;
}
