use async_trait::async_trait;

use ibc_relayer_components::chain::traits::queries::unreceived_packets::CanQueryUnreceivedPacketSequences;

use crate::one_for_all::traits::chain::OfaIbcChain;
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
        sequences: &[Counterparty::Sequence],
    ) -> Result<(Vec<Self::Sequence>, Self::Height), Self::Error> {
        let unreceived_packets = self
            .chain
            .query_unreceived_packet_sequences(channel_id, port_id, sequences)
            .await?;
        Ok(unreceived_packets)
    }
}
