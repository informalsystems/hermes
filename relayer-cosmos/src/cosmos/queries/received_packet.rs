use async_trait::async_trait;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::QueryUnreceivedPacketsRequest;
use ibc_relayer_framework::traits::queries::received_packet::ReceivedPacketQuerier;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::error::Error;

#[async_trait]
impl<Chain, Counterparty> ReceivedPacketQuerier<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: ChainHandle,
    Counterparty: ChainHandle,
{
    async fn is_packet_received(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, Self::Error> {
        let unreceived_packet = self
            .handle
            .query_unreceived_packets(QueryUnreceivedPacketsRequest {
                port_id: port_id.clone(),
                channel_id: channel_id.clone(),
                packet_commitment_sequences: vec![*sequence],
            })
            .map_err(Error::relayer)?;

        let is_packet_received = unreceived_packet.is_empty();

        Ok(is_packet_received)
    }
}
