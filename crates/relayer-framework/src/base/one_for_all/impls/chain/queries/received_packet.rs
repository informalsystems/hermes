use async_trait::async_trait;

use crate::base::chain::traits::queries::received_packet::{
    CanQueryReceivedPacket, ReceivedPacketQuerier,
};
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::common::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

pub struct SendReceivedPacketQueryToOfa;

#[async_trait]
impl<Chain, Counterparty>
    ReceivedPacketQuerier<OfaChainWrapper<Chain>, OfaChainWrapper<Counterparty>>
    for SendReceivedPacketQueryToOfa
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn query_is_packet_received(
        chain: &OfaChainWrapper<Chain>,
        port_id: &Chain::PortId,
        channel_id: &Chain::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Chain::Error> {
        let is_received = chain
            .chain
            .is_packet_received(port_id, channel_id, sequence)
            .await?;

        Ok(is_received)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanQueryReceivedPacket<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn query_is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Self::Error> {
        SendReceivedPacketQueryToOfa::query_is_packet_received(self, port_id, channel_id, sequence)
            .await
    }
}
