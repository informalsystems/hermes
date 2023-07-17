use async_trait::async_trait;
use ibc_relayer_components::chain::traits::message_builders::ack_packet::{
    CanBuildAckPacketMessage, CanBuildAckPacketPayload,
};
use ibc_relayer_components::chain::traits::types::packets::ack::HasAckPacketPayload;

use crate::one_for_all::traits::chain::OfaIbcChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> HasAckPacketPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type AckPacketPayload = Chain::AckPacketPayload;
}

#[async_trait]
impl<Chain, Counterparty> CanBuildAckPacketPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn build_ack_packet_payload(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<Self::AckPacketPayload, Self::Error> {
        self.chain
            .build_ack_packet_payload(height, packet, ack)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildAckPacketMessage<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn build_ack_packet_message(
        &self,
        payload: Counterparty::AckPacketPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain.build_ack_packet_message(payload).await
    }
}
