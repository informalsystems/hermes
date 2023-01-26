use async_trait::async_trait;

use crate::base::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::base::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanRelayReceivePacket: HasRelayTypes
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
    async fn relay_receive_packet(
        &self,
        source_height: &Height<Self::SrcChain>,
        packet: &Self::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>>, Self::Error>;
}

#[async_trait]
pub trait ReceivePacketRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
{
    async fn relay_receive_packet(
        context: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>;
}
