use async_trait::async_trait;

use ibc_relayer_components::chain::traits::queries::unreceived_packets::{
    CanQuerySendPacketsFromSequences, CanQueryUnreceivedPacketSequences,
};

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> CanQueryUnreceivedPacketSequences<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty> + OfaChainTypes,
    Counterparty: OfaIbcChain<Chain>,
{
    /// Given a list of counterparty commitment sequences,
    /// return a filtered list of sequences which the chain
    /// has not received the packet from the counterparty chain.
    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &Chain::ChannelId,
        port_id: &Chain::PortId,
        sequences: &[Counterparty::Sequence],
    ) -> Result<Vec<Counterparty::Sequence>, Self::Error> {
        let unreceived_packet_sequences = self
            .chain
            .query_unreceived_packet_sequences(channel_id, port_id, sequences)
            .await?;

        Ok(unreceived_packet_sequences)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanQuerySendPacketsFromSequences<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty> + OfaChainTypes,
    Counterparty: OfaIbcChain<Chain>,
{
    /// Given a list of sequences, a channel and port will query a list of outgoing
    /// packets which have not been relayed.
    async fn query_unreceived_packets(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequences: &[Self::Sequence],
        height: &Self::Height,
    ) -> Result<Vec<Self::OutgoingPacket>, Self::Error> {
        let unreceived_packet = self
            .chain
            .query_unreceived_packets(
                channel_id,
                port_id,
                counterparty_channel_id,
                counterparty_port_id,
                sequences,
                height,
            )
            .await?;
        Ok(unreceived_packet)
    }
}
