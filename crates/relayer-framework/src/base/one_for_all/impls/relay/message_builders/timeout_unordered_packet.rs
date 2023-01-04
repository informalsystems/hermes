use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::impls::packet_relayers::timeout_unordered::wait_timeout::WaitTimeoutUnorderedPacketMessageBuilder;
use crate::base::relay::traits::messages::timeout_unordered_packet::{
    CanBuildTimeoutUnorderedPacketMessage, TimeoutUnorderedPacketMessageBuilder,
};
use crate::std_prelude::*;

pub struct BuildTimeoutUnorderedPacketMessageFromOfa;

#[async_trait]
impl<Relay> CanBuildTimeoutUnorderedPacketMessage for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    WaitTimeoutUnorderedPacketMessageBuilder<BuildTimeoutUnorderedPacketMessageFromOfa>:
        TimeoutUnorderedPacketMessageBuilder<Self>,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<<Relay::SrcChain as OfaChainTypes>::Message, Relay::Error> {
        <WaitTimeoutUnorderedPacketMessageBuilder<BuildTimeoutUnorderedPacketMessageFromOfa>>::build_timeout_unordered_packet_message(
            self,
            destination_height,
            packet,
        )
        .await
    }
}
