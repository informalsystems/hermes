use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::impls::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::{
    CanRelayTimeoutUnorderedPacket, TimeoutUnorderedPacketRelayer,
};
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanRelayTimeoutUnorderedPacket for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    BaseTimeoutUnorderedPacketRelayer: TimeoutUnorderedPacketRelayer<Self>,
{
    async fn relay_timeout_unordered_packet(
        &self,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<(), Self::Error> {
        BaseTimeoutUnorderedPacketRelayer::relay_timeout_unordered_packet(
            self,
            destination_height,
            packet,
        )
        .await
    }
}
