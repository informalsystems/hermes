use http::uri::Uri;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_proto::cosmos::base::tendermint::v1beta1::service_client::ServiceClient;
use ibc_proto::cosmos::base::tendermint::v1beta1::GetNodeInfoRequest;

use crate::chain::cosmos::version::Specs;
use crate::error::Error;

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
