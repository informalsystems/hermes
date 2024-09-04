use http::uri::Uri;

use ibc_proto::ibc::core::connection::v1::query_client::QueryClient;
use ibc_proto::ibc::core::connection::v1::Params;
use ibc_proto::ibc::core::connection::v1::QueryConnectionParamsRequest;

use crate::config::default::max_grpc_decoding_size;
use crate::error::Error;
use crate::util::create_grpc_client;

/// Uses the GRPC client to retrieve the connection params
pub async fn query_connection_params(grpc_address: &Uri) -> Result<Params, Error> {
    let mut client = create_grpc_client(grpc_address.clone(), QueryClient::new).await?;

    client = client.max_decoding_message_size(max_grpc_decoding_size().get_bytes() as usize);

    let request = tonic::Request::new(QueryConnectionParamsRequest {});

    let response = client
        .connection_params(request)
        .await
        .map(|r| r.into_inner())
        .map_err(|e| Error::grpc_status(e, "query_connection_params".to_owned()))?;

    // Querying connection params might not be found
    let params = response.params.ok_or_else(Error::empty_connection_params)?;

    Ok(params)
}
