use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait AckPacketRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
{
    async fn relay_ack_packet(
        context: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait HasAckPacketRelayer: HasRelayTypes
where
    Self::DstChain: HasIbcEvents<Self::SrcChain>,
{
    type AckPacketRelayer: AckPacketRelayer<Self>;

    async fn relay_ack_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
        ack: &WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>,
    ) -> Result<(), Self::Error> {
        Self::AckPacketRelayer::relay_ack_packet(self, destination_height, packet, ack).await
    }
}
