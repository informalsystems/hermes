use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::traits::messages::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketMessage;
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay: OfaBaseRelay> CanBuildTimeoutUnorderedPacketMessage for OfaRelayWrapper<Relay> {
    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<<Relay::SrcChain as OfaChainTypes>::Message, Relay::Error> {
        let message = self
            .relay
            .build_timeout_unordered_packet_message(destination_height, packet)
            .await?;

        Ok(message)
    }
}
