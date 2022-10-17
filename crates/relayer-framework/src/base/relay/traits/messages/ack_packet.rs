use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::types::aliases::{Height, Message, WriteAcknowledgementEvent};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait AckPacketMessageBuilder<Relay: HasRelayTypes>
where
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
{
    async fn build_ack_packet_message(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}

#[async_trait]
pub trait HasAckPacketMessageBuilder: HasRelayTypes
where
    Self::DstChain: HasIbcEvents<Self::SrcChain>,
{
    type AckPacketMessageBuilder: AckPacketMessageBuilder<Self>;

    async fn build_ack_packet_message(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
        ack: &WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>,
    ) -> Result<Message<Self::SrcChain>, Self::Error> {
        Self::AckPacketMessageBuilder::build_ack_packet_message(
            self,
            destination_height,
            packet,
            ack,
        )
        .await
    }
}
