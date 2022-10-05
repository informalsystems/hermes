use http::uri::Uri;

use ibc_proto::ibc::applications::transfer::v1::{
    query_client::QueryClient, QueryDenomTraceRequest,
};

use crate::{denom::DenomTrace, error::Error};

// Uses the GRPC client to retrieve the denom trace for a specific hash
pub async fn query_denom_trace(grpc_address: &Uri, hash: &str) -> Result<DenomTrace, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let request = tonic::Request::new(QueryDenomTraceRequest {
        hash: hash.to_owned(),
    });

    let response = client
        .denom_trace(request)
        .await
        .map(|r| r.into_inner())
        .map_err(Error::grpc_status)?;

    let denom_trace = response
        .denom_trace
        .ok_or_else(|| Error::empty_denom_trace(hash.to_owned()))?;

    Ok(DenomTrace {
        path: denom_trace.path,
        base_denom: denom_trace.base_denom,
    })
}
