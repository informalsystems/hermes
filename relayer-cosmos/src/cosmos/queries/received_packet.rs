use async_trait::async_trait;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::QueryUnreceivedPacketsRequest;
use ibc_relayer_framework::traits::queries::received_packet::{
    CanQueryReceivedPacket, ReceivedPacketQuerier,
};

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::error::Error;

pub struct CosmosReceivedPacketQuerier;

#[async_trait]
impl<Chain, Counterparty>
    ReceivedPacketQuerier<CosmosChainContext<Chain>, CosmosChainContext<Counterparty>>
    for CosmosReceivedPacketQuerier
where
    Chain: ChainHandle,
    Counterparty: ChainHandle,
{
    async fn is_packet_received(
        chain: &CosmosChainContext<Chain>,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, Error> {
        let unreceived_packet = chain
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

impl<Chain, Counterparty> CanQueryReceivedPacket<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: ChainHandle,
    Counterparty: ChainHandle,
{
    type ReceivedPacketQuerier = CosmosReceivedPacketQuerier;
}
