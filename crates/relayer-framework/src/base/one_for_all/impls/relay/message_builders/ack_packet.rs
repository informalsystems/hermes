use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::traits::messages::ack_packet::CanBuildAckPacketMessage;
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay: OfaBaseRelay> CanBuildAckPacketMessage for OfaRelayWrapper<Relay> {
    async fn build_ack_packet_message(
        &self,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
        ack: &<Relay::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<<Relay::SrcChain as OfaChainTypes>::Message, Relay::Error> {
        let message = self
            .relay
            .build_ack_packet_message(destination_height, packet, ack)
            .await?;

        Ok(message)
    }
}
