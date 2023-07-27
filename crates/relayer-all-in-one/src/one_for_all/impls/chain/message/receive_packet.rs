use async_trait::async_trait;
use ibc_relayer_components::chain::traits::message_builders::receive_packet::{
    CanBuildReceivePacketMessage, CanBuildReceivePacketPayload,
};
use ibc_relayer_components::chain::traits::types::packets::receive::HasReceivePacketPayload;

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> HasReceivePacketPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type ReceivePacketPayload = Chain::ReceivePacketPayload;
}

#[async_trait]
impl<Chain, Counterparty> CanBuildReceivePacketPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_receive_packet_payload(
        &self,
        height: &Self::Height,
        packet: &Self::OutgoingPacket,
    ) -> Result<Self::ReceivePacketPayload, Self::Error> {
        self.chain
            .build_receive_packet_payload(height, packet)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildReceivePacketMessage<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_receive_packet_message(
        &self,
        payload: Counterparty::ReceivePacketPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain.build_receive_packet_message(payload).await
    }
}
