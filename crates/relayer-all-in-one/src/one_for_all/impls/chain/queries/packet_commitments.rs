use async_trait::async_trait;

use ibc_relayer_components::chain::traits::queries::packet_commitments::CanQueryPacketCommitments;

use crate::one_for_all::traits::chain::OfaIbcChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> CanQueryPacketCommitments<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn query_packet_commitments(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
    ) -> Result<Vec<Counterparty::Sequence>, Self::Error> {
        let sequences = self
            .chain
            .query_packet_commitments(channel_id, port_id)
            .await?;
        Ok(sequences)
    }
}
