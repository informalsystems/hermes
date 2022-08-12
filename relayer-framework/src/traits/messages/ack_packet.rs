use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::ibc_event::HasIbcEvents;
use crate::traits::contexts::relay::RelayContext;
use crate::types::aliases::{Height, IbcMessage, WriteAcknowledgementEvent};

#[async_trait]
pub trait AckPacketMessageBuilder<Relay: RelayContext>
where
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
{
    async fn build_ack_packet_message(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<IbcMessage<Relay::SrcChain, Relay::DstChain>, Relay::Error>;
}

#[async_trait]
pub trait CanBuildAckPacketMessage: RelayContext
where
    Self::DstChain: HasIbcEvents<Self::SrcChain>,
{
    type AckPacketMessageBuilder: AckPacketMessageBuilder<Self>;

    async fn build_ack_packet_message(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
        ack: &WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>,
    ) -> Result<IbcMessage<Self::SrcChain, Self::DstChain>, Self::Error> {
        Self::AckPacketMessageBuilder::build_ack_packet_message(
            self,
            destination_height,
            packet,
            ack,
        )
        .await
    }
}
