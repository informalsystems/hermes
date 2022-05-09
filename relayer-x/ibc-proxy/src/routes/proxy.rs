use axum::response::IntoResponse;
use color_eyre::eyre::Context;
use hyper::{client::HttpConnector, Body};
use tendermint_rpc::Url;
use tracing::info;

use crate::{
    error::ReportError,
    jsonrpc::{JsonRpc, JsonRpcRequest},
};

pub type HttpClient = hyper::Client<HttpConnector>;

#[tracing::instrument(skip(rpc_client, rpc_addr, body))]
pub async fn proxy(
    rpc_client: &HttpClient,
    rpc_addr: &Url,
    body: JsonRpc<serde_json::Value>,
) -> Result<axum::response::Response, ReportError> {
    info!("proxying request");

    dbg!(&body);

    let request = JsonRpcRequest::new(body.method, body.id, body.params);
    let body = serde_json::to_string(&request).wrap_err("failed to serialize body to JSON")?;

    let request = hyper::Request::builder()
        .method("POST")
        .uri(rpc_addr.to_string().as_str())
        .header("Content-Type", "application/json")
        .body(Body::from(body))
        .wrap_err("failed to construct request")?;

    let response = rpc_client
        .request(request)
        .await
        .wrap_err("failed to proxy request")?;

    Ok(response.into_response())
}
