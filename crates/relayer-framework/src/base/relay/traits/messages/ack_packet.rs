use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasWriteAcknowledgementEvent;
use crate::base::chain::types::aliases::{Height, Message, WriteAcknowledgementEvent};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildAckPacketMessage: HasRelayTypes
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
    async fn build_ack_packet_message(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
        ack: &WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>,
    ) -> Result<Message<Self::SrcChain>, Self::Error>;
}

#[async_trait]
pub trait AckPacketMessageBuilder<Relay: HasRelayTypes>
where
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
{
    async fn build_ack_packet_message(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}
