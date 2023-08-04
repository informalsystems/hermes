use async_trait::async_trait;

use ibc_relayer_components::chain::traits::queries::send_packet::CanQuerySendPacketsFromSequences;

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> CanQuerySendPacketsFromSequences<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty> + OfaChainTypes,
    Counterparty: OfaIbcChain<Chain>,
{
    /// Given a list of sequences, a channel and port will query a list of outgoing
    /// packets which have not been relayed.
    async fn query_send_packets_from_sequences(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequences: &[Self::Sequence],
        // The height is given to query the packets from a specific height.
        // This height should be the same as the query height from the
        // `CanQueryPacketCommitments` made on the same chain.
        height: &Self::Height,
    ) -> Result<Vec<Self::OutgoingPacket>, Self::Error> {
        let send_packets = self
            .chain
            .query_send_packets_from_sequences(
                channel_id,
                port_id,
                counterparty_channel_id,
                counterparty_port_id,
                sequences,
                height,
            )
            .await?;
        Ok(send_packets)
    }
}
