use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::relay::OfaRelayComponents;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::packet_relayers::receive_packet::{
    CanRelayReceivePacket, ReceivePacketRelayer,
};
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Components> CanRelayReceivePacket for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    async fn relay_receive_packet(
        &self,
        source_height: &<Relay::SrcChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<Option<<Relay::DstChain as OfaChainTypes>::WriteAcknowledgementEvent>, Relay::Error>
    {
        Components::ReceivePacketRelayer::relay_receive_packet(self, source_height, packet).await
    }
}
