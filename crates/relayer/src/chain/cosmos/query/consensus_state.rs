use http::Uri;
use tracing::{debug, warn};

use ibc_relayer_types::{core::ics24_host::identifier::ChainId, Height};

use crate::{
    chain::requests::{QueryConsensusStateHeightsRequest, QueryConsensusStatesRequest},
    consensus_state::AnyConsensusStateWithHeight,
    error::Error,
    util::pretty::{PrettyConsensusStateWithHeight, PrettyHeight},
};

pub async fn query_consensus_state_heights(
    chain_id: &ChainId,
    grpc_addr: &Uri,
    request: QueryConsensusStateHeightsRequest,
) -> Result<Vec<Height>, Error> {
    crate::time!("query_consensus_state_heights");
    crate::telemetry!(query, chain_id, "query_consensus_state_heights");

    // Helper function to diagnose if the QueryConsensusStateHeightsRequest is unsupported
    // by matching on the error details.
    fn is_unsupported(status: &tonic::Status) -> bool {
        if status.code() != tonic::Code::Unimplemented {
            return false;
        }

        status
            .message()
            .contains("unknown method ConsensusStateHeights")
    }

    let mut client =
        ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(grpc_addr.clone())
            .await
            .map_err(Error::grpc_transport)?;

    let grpc_request = tonic::Request::new(request.clone().into());
    let grpc_response = client.consensus_state_heights(grpc_request).await;

    if let Err(ref e) = grpc_response {
        if is_unsupported(e) {
            debug!("QueryConsensusStateHeights is not supported by the chain, falling back on QueryConsensusStates");

            let states = query_consensus_states(
                chain_id,
                grpc_addr,
                QueryConsensusStatesRequest {
                    client_id: request.client_id,
                    pagination: request.pagination,
                },
            )
            .await?;

            return Ok(states.into_iter().map(|cs| cs.height).collect());
        }
    }

    let response = grpc_response.map_err(Error::grpc_status)?.into_inner();

    let mut heights: Vec<_> = response
        .consensus_state_heights
        .into_iter()
        .filter_map(|h| {
            Height::try_from(h.clone())
                .map_err(|e| {
                    warn!(
                        "failed to parse consensus state height {}. Error: {}",
                        PrettyHeight(&h),
                        e
                    )
                })
                .ok()
        })
        .collect();

    heights.sort_unstable();

    Ok(heights)
}

pub async fn query_consensus_states(
    _chain_id: &ChainId,
    grpc_addr: &Uri,
    request: QueryConsensusStatesRequest,
) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
    crate::time!("query_consensus_states");
    crate::telemetry!(query, _chain_id, "query_consensus_states");

    let mut client =
        ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(grpc_addr.clone())
            .await
            .map_err(Error::grpc_transport)?;

    let response = client
        .consensus_states(tonic::Request::new(request.into()))
        .await
        .map_err(Error::grpc_status)?
        .into_inner();

    let mut consensus_states: Vec<_> = response
        .consensus_states
        .into_iter()
        .filter_map(|cs| {
            AnyConsensusStateWithHeight::try_from(cs.clone())
                .map_err(|e| {
                    warn!(
                        "failed to parse consensus state {}. Error: {}",
                        PrettyConsensusStateWithHeight(&cs),
                        e
                    )
                })
                .ok()
        })
        .collect();

    consensus_states.sort_unstable_by_key(|cs| cs.height);

    Ok(consensus_states)
}
