use async_trait::async_trait;

use ibc_relayer_components::chain::traits::queries::unreceived_packets::{
    CanQueryUnreceivedPacketSequences, CanQueryUnreceivedPackets,
};

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> CanQueryUnreceivedPacketSequences<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        sequences: &[Self::Sequence],
    ) -> Result<(Vec<Self::Sequence>, Self::Height), Self::Error> {
        let unreceived_packet_sequences = self
            .chain
            .query_unreceived_packet_sequences(channel_id, port_id, sequences)
            .await?;
        Ok(unreceived_packet_sequences)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanQueryUnreceivedPackets<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty> + OfaChainTypes,
    Counterparty: OfaIbcChain<Chain>,
{
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
