use async_trait::async_trait;
use ibc_relayer_components::relay::traits::packet_relayers::receive_packet::{
    CanRelayReceivePacket, ReceivePacketRelayer,
};

use crate::one_for_all::components;
use crate::one_for_all::traits::chain::OfaChainTypes;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanRelayReceivePacket for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
    components::ReceivePacketRelayer: ReceivePacketRelayer<Self>,
{
    async fn relay_receive_packet(
        &self,
        source_height: &<Relay::SrcChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<Option<<Relay::DstChain as OfaChainTypes>::WriteAcknowledgementEvent>, Relay::Error>
    {
        components::ReceivePacketRelayer::relay_receive_packet(self, source_height, packet).await
    }
}
