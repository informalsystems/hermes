use alloc::sync::Arc;
use ibc_proto::ibc::core::channel::v1::query_client::QueryClient as ChannelQueryClient;
use ibc_relayer::chain::cosmos::query::packet_query;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    Qualified, QueryHeight, QueryPacketCommitmentsRequest, QueryPacketEventDataRequest,
    QueryUnreceivedPacketsRequest,
};
use ibc_relayer_all_in_one::one_for_all::traits::chain::OfaChain;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer_types::events::WithBlockDataType;
use ibc_relayer_types::Height;
use tendermint_rpc::{Client, Order};
use tonic::Request;

use crate::contexts::chain::CosmosChain;
use crate::types::error::{BaseError, Error};

pub async fn query_packet_commitments<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    channel_id: &ChannelId,
    port_id: &PortId,
) -> Result<Vec<Sequence>, Error> {
    let mut client =
        ChannelQueryClient::connect(chain.tx_context.tx_context.tx_config.grpc_address.clone())
            .await
            .map_err(BaseError::grpc_transport)?;

    let raw_request = QueryPacketCommitmentsRequest {
        port_id: port_id.clone(),
        channel_id: channel_id.clone(),
        pagination: None,
    };

    let request = Request::new(raw_request.into());

    let response = client
        .packet_commitments(request)
        .await
        .map_err(|e| BaseError::grpc_status(e, "query_packet_commitments".to_owned()))?
        .into_inner();

    let commitment_sequences: Vec<Sequence> = response
        .commitments
        .into_iter()
        .map(|packet_state| packet_state.sequence.into())
        .collect();

    Ok(commitment_sequences)
}

async fn query_unreceived_packet_sequences<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    channel_id: &ChannelId,
    port_id: &PortId,
    sequences: &[Sequence],
) -> Result<(Vec<Sequence>, Height), Error> {
    let mut client =
        ChannelQueryClient::connect(chain.tx_context.tx_context.tx_config.grpc_address.clone())
            .await
            .map_err(BaseError::grpc_transport)?;

    let raw_request = QueryUnreceivedPacketsRequest {
        port_id: port_id.clone(),
        channel_id: channel_id.clone(),
        packet_commitment_sequences: sequences.to_vec(),
    };

    let request = Request::new(raw_request.into());

    let response = client
        .unreceived_packets(request)
        .await
        .map_err(|e| BaseError::grpc_status(e, "query_packet_commitments".to_owned()))?
        .into_inner();

    let raw_height = response
        .height
        .ok_or_else(|| BaseError::missing_height("query_unreceived_packets".to_owned()))?;
    let height = raw_height.try_into().map_err(BaseError::ics02)?;
    let response_sequences = response.sequences.into_iter().map(|s| s.into()).collect();
    Ok((response_sequences, height))
}

pub async fn query_unreceived_packets<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    channel_id: &ChannelId,
    port_id: &PortId,
    counterparty_channel_id: &ChannelId,
    counterparty_port_id: &PortId,
    sequences: &[Sequence],
) -> Result<Vec<Packet>, Error> {
    let (unreceived_sequences, height) =
        query_unreceived_packet_sequences(chain, channel_id, port_id, sequences).await?;
    let request = QueryPacketEventDataRequest {
        event_id: WithBlockDataType::SendPacket,
        source_channel_id: channel_id.clone(),
        source_port_id: port_id.clone(),
        destination_channel_id: counterparty_channel_id.clone(),
        destination_port_id: counterparty_port_id.clone(),
        sequences: unreceived_sequences.to_vec(),
        height: Qualified::SmallerEqual(QueryHeight::Specific(height)),
    };
    let mut events = vec![];
    for sequence in sequences.iter() {
        let query = packet_query(&request, *sequence);
        let response = chain
            .tx_context
            .tx_context
            .rpc_client
            .tx_search(query, false, 1, 10, Order::Descending)
            .await
            .unwrap();
        for tx in response.txs.iter() {
            let mut event = tx
                .tx_result
                .events
                .iter()
                .map(|event| Arc::new(event.clone()))
                .collect();
            events.append(&mut event);
        }
    }

    let send_packets = events
        .iter()
        .filter_map(<CosmosChain<Chain> as OfaChain>::try_extract_send_packet_event)
        .map(|event| {
            <CosmosChain<Chain> as OfaChain>::extract_packet_from_send_packet_event(&event)
        })
        .collect();

    Ok(send_packets)
}
