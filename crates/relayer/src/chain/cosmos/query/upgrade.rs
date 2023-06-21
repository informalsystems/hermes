use http::uri::Uri;

use crate::config::default::max_grpc_decoding_size;
use crate::error::Error;
use ibc_proto::ibc::core::channel::v1::{
    query_client::QueryClient, QueryUpgradeRequest, QueryUpgradeResponse,
};

/// Query the upgrade for a port and channel.
pub async fn query_upgrade(
    grpc_address: &Uri,
    request: QueryUpgradeRequest,
) -> Result<QueryUpgradeResponse, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    client = client.max_decoding_message_size(max_grpc_decoding_size().get_bytes() as usize);

    let response = client
        .upgrade(tonic::Request::new(request))
        .await
        .map_err(|e| Error::grpc_status(e, "query_incentivized_packet".to_owned()))?;

    Ok(response.into_inner())
}
