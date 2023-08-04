use async_trait::async_trait;

use ibc_relayer_components::chain::types::aliases::{ChannelId, PortId};
use ibc_relayer_components::relay::impls::packet_clear::receive_packets_clear::ReceivePacketClearRelayer;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::packet_clear::{
    CanClearReceivePackets, ReceivePacketClearer,
};

use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanClearReceivePackets for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn clear_receive_packets(
        &self,
        src_channel_id: &ChannelId<
            <OfaRelayWrapper<Relay> as HasRelayChains>::SrcChain,
            <OfaRelayWrapper<Relay> as HasRelayChains>::DstChain,
        >,
        src_port_id: &PortId<
            <OfaRelayWrapper<Relay> as HasRelayChains>::SrcChain,
            <OfaRelayWrapper<Relay> as HasRelayChains>::DstChain,
        >,
        dst_channel_id: &ChannelId<
            <OfaRelayWrapper<Relay> as HasRelayChains>::DstChain,
            <OfaRelayWrapper<Relay> as HasRelayChains>::SrcChain,
        >,
        dst_port_id: &PortId<
            <OfaRelayWrapper<Relay> as HasRelayChains>::DstChain,
            <OfaRelayWrapper<Relay> as HasRelayChains>::SrcChain,
        >,
    ) -> Result<(), Relay::Error> {
        ReceivePacketClearRelayer::clear_receive_packets(
            self,
            src_channel_id,
            src_port_id,
            dst_channel_id,
            dst_port_id,
        )
        .await
    }
}
