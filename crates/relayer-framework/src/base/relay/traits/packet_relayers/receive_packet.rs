use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait ReceivePacketRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
{
    async fn relay_receive_packet(
        context: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>;
}

#[async_trait]
pub trait HasReceivePacketRelayer: HasRelayTypes
where
    Self::DstChain: HasIbcEvents<Self::SrcChain>,
{
    type ReceivePacketRelayer: ReceivePacketRelayer<Self>;

    async fn relay_receive_packet(
        &self,
        source_height: &Height<Self::SrcChain>,
        packet: &Self::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>>, Self::Error>
    {
        Self::ReceivePacketRelayer::relay_receive_packet(self, source_height, packet).await
    }
}
