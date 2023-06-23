use async_trait::async_trait;
use ibc_relayer_components::relay::impls::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use ibc_relayer_components::relay::traits::packet_relayers::receive_packet::{
    CanRelayReceivePacket, ReceivePacketRelayer,
};

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanRelayReceivePacket for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    SkipReceivedPacketRelayer<BaseReceivePacketRelayer>: ReceivePacketRelayer<Self>,
{
    async fn relay_receive_packet(
        &self,
        source_height: &<Relay::SrcChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<Option<<Relay::DstChain as OfaChainTypes>::WriteAcknowledgementEvent>, Relay::Error>
    {
        <SkipReceivedPacketRelayer<BaseReceivePacketRelayer>>::relay_receive_packet(
            self,
            source_height,
            packet,
        )
        .await
    }
}
