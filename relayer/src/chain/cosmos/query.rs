use http::uri::Uri;
use ibc::core::ics02_client::client_consensus::QueryClientEventRequest;
use ibc::core::ics04_channel::channel::QueryPacketEventDataRequest;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics23_commitment::merkle::convert_tm_to_ics_merkle_proof;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::query::QueryTxHash;
use ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient;
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, EthAccount, QueryAccountRequest};
use ibc_proto::cosmos::base::tendermint::v1beta1::service_client::ServiceClient;
use ibc_proto::cosmos::base::tendermint::v1beta1::GetNodeInfoRequest;
use prost::Message;
use tendermint::abci::Path as TendermintABCIPath;
use tendermint::block::Height;
use tendermint_rpc::query::Query;
use tendermint_rpc::{Client, HttpClient, Url};
use tracing::info;

use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::version::Specs;
use crate::chain::QueryResponse;
use crate::error::Error;

pub async fn get_or_fetch_account<'a>(
    grpc_address: &Uri,
    account_address: &str,
    m_account: &'a mut Option<Account>,
) -> Result<&'a mut Account, Error> {
    match m_account {
        Some(account) => Ok(account),
        None => {
            let account = query_account(grpc_address, account_address).await?;
            *m_account = Some(account.into());

            Ok(m_account
                .as_mut()
                .expect("account was supposedly just cached"))
        }
    }
}

pub async fn refresh_account<'a>(
    grpc_address: &Uri,
    account_address: &str,
    m_account: &'a mut Account,
) -> Result<(), Error> {
    let account = query_account(grpc_address, account_address).await?;

    info!(
        sequence = %account.sequence,
        number = %account.account_number,
        "refresh: retrieved account",
    );

    *m_account = account.into();

    Ok(())
}

/// Uses the GRPC client to retrieve the account sequence
pub async fn query_account(
    grpc_address: &Uri,
    account_address: &str,
) -> Result<BaseAccount, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let request = tonic::Request::new(QueryAccountRequest {
        address: account_address.to_string(),
    });

    let response = client.account(request).await;

    // Querying for an account might fail, i.e. if the account doesn't actually exist
    let resp_account = match response.map_err(Error::grpc_status)?.into_inner().account {
        Some(account) => account,
        None => return Err(Error::empty_query_account(account_address.to_string())),
    };

    if resp_account.type_url == "/cosmos.auth.v1beta1.BaseAccount" {
        Ok(BaseAccount::decode(resp_account.value.as_slice())
            .map_err(|e| Error::protobuf_decode("BaseAccount".to_string(), e))?)
    } else if resp_account.type_url.ends_with(".EthAccount") {
        Ok(EthAccount::decode(resp_account.value.as_slice())
            .map_err(|e| Error::protobuf_decode("EthAccount".to_string(), e))?
            .base_account
            .ok_or_else(Error::empty_base_account)?)
    } else {
        Err(Error::unknown_account_type(resp_account.type_url))
    }
}

pub fn packet_query(request: &QueryPacketEventDataRequest, seq: Sequence) -> Query {
    tendermint_rpc::query::Query::eq(
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
    tendermint_rpc::query::Query::eq(
        format!("{}.client_id", request.event_id.as_str()),
        request.client_id.to_string(),
    )
    .and_eq(
        format!("{}.consensus_height", request.event_id.as_str()),
        format!(
            "{}-{}",
            request.consensus_height.revision_number, request.consensus_height.revision_height
        ),
    )
}

pub fn tx_hash_query(request: &QueryTxHash) -> Query {
    tendermint_rpc::query::Query::eq("tx.hash", request.0.to_string())
}

/// Perform a generic `abci_query`, and return the corresponding deserialized response data.
pub async fn abci_query(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    path: TendermintABCIPath,
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
