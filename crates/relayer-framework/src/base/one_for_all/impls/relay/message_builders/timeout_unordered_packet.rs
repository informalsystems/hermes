use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayPreset};
use crate::base::relay::traits::messages::timeout_unordered_packet::{
    CanBuildTimeoutUnorderedPacketMessage, TimeoutUnorderedPacketMessageBuilder,
};
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

pub struct BuildTimeoutUnorderedPacketMessageFromOfa;

#[async_trait]
impl<Relay: OfaBaseRelay> TimeoutUnorderedPacketMessageBuilder<OfaRelayWrapper<Relay>>
    for BuildTimeoutUnorderedPacketMessageFromOfa
{
    async fn build_timeout_unordered_packet_message(
        context: &OfaRelayWrapper<Relay>,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<<Relay::SrcChain as OfaChainTypes>::Message, Relay::Error> {
        let message = context
            .relay
            .build_timeout_unordered_packet_message(destination_height, packet)
            .await?;

        Ok(message)
    }
}

#[async_trait]
impl<Relay, Preset> CanBuildTimeoutUnorderedPacketMessage for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaRelayPreset<Relay>,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<<Relay::SrcChain as OfaChainTypes>::Message, Relay::Error> {
        Preset::TimeoutUnorderedPacketMessageBuilder::build_timeout_unordered_packet_message(
            self,
            destination_height,
            packet,
        )
        .await
    }
}
