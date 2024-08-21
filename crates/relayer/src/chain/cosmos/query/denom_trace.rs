use http::uri::Uri;
use serde::Deserialize;

use crate::denom::DenomTrace;
use crate::error::Error;

/// Extracted `QueryDenomTraceRequest` since ibc-go removed it from
/// the proto definitions, https://github.com/cosmos/ibc-go/pull/6433
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryDenomTraceRequest {
    /// hash (in hex format) or denom (full denom with ibc prefix) of the denomination trace information.
    #[prost(string, tag = "1")]
    pub hash: ::prost::alloc::string::String,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Deserialize)]
pub struct QueryDenomTraceResponse {
    /// denom_trace returns the requested denomination trace information.
    pub denom_trace: ::core::option::Option<DenomTrace>,
}

// Uses the GRPC client to retrieve the denom trace for a specific hash
pub async fn query_denom_trace(rpc_address: &Uri, hash: &str) -> Result<DenomTrace, Error> {
    let url = format!(
        "{}abci_query?path=\"/ibc.applications.transfer.v1.Query/QueryDenomTraceRequest\"&hash={}",
        rpc_address, hash
    );

    let response = reqwest::get(&url).await.map_err(Error::http_request)?;

    if !response.status().is_success() {
        return Err(Error::http_response(response.status()));
    }

    let result: QueryDenomTraceResponse =
        response.json().await.map_err(Error::http_response_body)?;

    let denom_trace = result
        .denom_trace
        .ok_or_else(|| Error::empty_denom_trace(hash.to_owned()))?;

    Ok(DenomTrace {
        path: denom_trace.path,
        base_denom: denom_trace.base_denom,
    })
}
