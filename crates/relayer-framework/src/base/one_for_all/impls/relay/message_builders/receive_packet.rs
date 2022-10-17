use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::traits::messages::receive_packet::CanBuildReceivePacketMessage;
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay: OfaBaseRelay> CanBuildReceivePacketMessage for OfaRelayWrapper<Relay> {
    async fn build_receive_packet_message(
        &self,
        height: &<Relay::SrcChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<<Relay::DstChain as OfaChainTypes>::Message, Relay::Error> {
        let message = self
            .relay
            .build_receive_packet_message(height, packet)
            .await?;

        Ok(message)
    }
}
