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
    /// Query the sequences of the packets that the chain has committed to be
    /// sent to the counterparty chain, of which the full packet relaying is not
    /// yet completed. Once the chain receives the ack from the counterparty
    /// chain, a given sequence should be removed from the packet commitment list.
    async fn query_packet_commitments(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
    ) -> Result<(Vec<Self::Sequence>, Self::Height), Self::Error> {
        let (sequences, height) = self
            .chain
            .query_packet_commitments(channel_id, port_id)
            .await?;
        Ok((sequences, height))
    }
}
