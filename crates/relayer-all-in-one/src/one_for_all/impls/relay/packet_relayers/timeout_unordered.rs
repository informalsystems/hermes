use async_trait::async_trait;

use crate::one_for_all::components;
use crate::one_for_all::traits::chain::OfaChainTypes;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;
use ibc_relayer_components::relay::traits::packet_relayers::timeout_unordered_packet::{
    CanRelayTimeoutUnorderedPacket, TimeoutUnorderedPacketRelayer,
};

#[async_trait]
impl<Relay> CanRelayTimeoutUnorderedPacket for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
    components::TimeoutUnorderedPacketRelayer: TimeoutUnorderedPacketRelayer<Self>,
{
    async fn relay_timeout_unordered_packet(
        &self,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<(), Self::Error> {
        components::TimeoutUnorderedPacketRelayer::relay_timeout_unordered_packet(
            self,
            destination_height,
            packet,
        )
        .await
    }
}
