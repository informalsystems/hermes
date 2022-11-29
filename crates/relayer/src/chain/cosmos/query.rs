use http::uri::Uri;
use ibc_proto::cosmos::base::tendermint::v1beta1::service_client::ServiceClient;
use ibc_proto::cosmos::base::tendermint::v1beta1::GetNodeInfoRequest;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics23_commitment::merkle::{
    convert_tm_to_ics_merkle_proof, MerkleProof,
};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint::block::Height;
use tendermint_rpc::query::Query;
use tendermint_rpc::{Client, HttpClient, Url};

use crate::chain::cosmos::version::Specs;
use crate::chain::requests::{QueryClientEventRequest, QueryPacketEventDataRequest, QueryTxHash};
use crate::error::Error;

pub mod account;
pub mod balance;
pub mod denom_trace;
pub mod fee;
pub mod status;
pub mod tx;

/// Generic query response type
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryResponse {
    pub value: Vec<u8>,
    pub proof: Option<MerkleProof>,
    pub height: Height,
}

pub fn packet_query(request: &QueryPacketEventDataRequest, seq: Sequence) -> Query {
    Query::eq(
        format!("{}.packet_src_channel", request.event_id.as_str()),
        request.source_channel_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_src_port", request.event_id.as_str()),
        request.source_port_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_dst_channel", request.event_id.as_str()),
        request.destination_channel_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_dst_port", request.event_id.as_str()),
        request.destination_port_id.to_string(),
    )
    .and_eq(
        format!("{}.packet_sequence", request.event_id.as_str()),
        seq.to_string(),
    )
}

pub fn header_query(request: &QueryClientEventRequest) -> Query {
    Query::eq(
        format!("{}.client_id", request.event_id.as_str()),
        request.client_id.to_string(),
    )
    .and_eq(
        format!("{}.consensus_height", request.event_id.as_str()),
        format!(
            "{}-{}",
            request.consensus_height.revision_number(),
            request.consensus_height.revision_height()
        ),
    )
}

pub fn tx_hash_query(request: &QueryTxHash) -> Query {
    Query::eq("tx.hash", request.0.to_string())
}

/// Perform a generic `abci_query`, and return the corresponding deserialized response data.
pub async fn abci_query(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    path: String,
    data: String,
    height: Height,
    prove: bool,
) -> Result<QueryResponse, Error> {
    let height = if height.value() == 0 {
        None
    } else {
        Some(height)
    };

    // Use the Tendermint-rs RPC client to do the query.
    let response = rpc_client
        .abci_query(Some(path), data.into_bytes(), height, prove)
        .await
        .map_err(|e| Error::rpc(rpc_address.clone(), e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        return Err(Error::abci_query(response));
    }

    if prove && response.proof.is_none() {
        // Fail due to empty proof
        return Err(Error::empty_response_proof());
    }

    let proof = response
        .proof
        .map(|p| convert_tm_to_ics_merkle_proof(&p))
        .transpose()
        .map_err(Error::ics23)?;

    let response = QueryResponse {
        value: response.value,
        height: response.height,
        proof,
    };

    Ok(response)
}

/// Queries the chain to obtain the version information.
pub async fn fetch_version_specs(chain_id: &ChainId, grpc_address: &Uri) -> Result<Specs, Error> {
    let grpc_addr_string = grpc_address.to_string();

    // Construct a gRPC client
    let mut client = ServiceClient::connect(grpc_address.clone())
        .await
        .map_err(|e| {
            Error::fetch_version_grpc_transport(
                chain_id.clone(),
                grpc_addr_string.clone(),
                "tendermint::ServiceClient".to_string(),
                e,
            )
        })?;

    let request = tonic::Request::new(GetNodeInfoRequest {});

    let response = client.get_node_info(request).await.map_err(|e| {
        Error::fetch_version_grpc_status(
            chain_id.clone(),
            grpc_addr_string.clone(),
            "tendermint::ServiceClient".to_string(),
            e,
        )
    })?;

    let version = response.into_inner().application_version.ok_or_else(|| {
        Error::fetch_version_invalid_version_response(
            chain_id.clone(),
            grpc_addr_string.clone(),
            "tendermint::GetNodeInfoRequest".to_string(),
        )
    })?;

    // Parse the raw version info into a domain-type `version::Specs`
    version
        .try_into()
        .map_err(|e| Error::fetch_version_parsing(chain_id.clone(), grpc_addr_string.clone(), e))
}
