use async_trait::async_trait;

use crate::base::chain::traits::message::receive_packet::{
    CanBuildReceivePacketMessage, ReceivePacketMessageBuilder,
};
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

pub struct BuildReceivePacketMessageFromOfa;

#[async_trait]
impl<Chain, Counterparty>
    ReceivePacketMessageBuilder<OfaChainWrapper<Chain>, OfaChainWrapper<Counterparty>>
    for BuildReceivePacketMessageFromOfa
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    async fn build_receive_packet_message(
        chain: &OfaChainWrapper<Chain>,
        height: &Chain::Height,
        packet: &Chain::OutgoingPacket,
    ) -> Result<Counterparty::Message, Chain::Error> {
        chain
            .chain
            .build_receive_packet_message(height, packet)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildReceivePacketMessage<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    async fn build_receive_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::OutgoingPacket,
    ) -> Result<Counterparty::Message, Self::Error> {
        self.chain
            .build_receive_packet_message(height, packet)
            .await
    }
}
