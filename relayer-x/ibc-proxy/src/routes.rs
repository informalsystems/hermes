use axum::{
    response::{IntoResponse, Response},
    Extension,
};

use sqlx::PgPool;
use tendermint_rpc::Url;
use tracing::{debug, error, info};

use crate::{error::ReportError, jsonrpc::JsonRpc};

use self::proxy::HttpClient;

use crate::search::Search;

pub mod proxy;
pub use proxy::proxy;

pub mod tx;
pub use tx::tx_search;

pub mod packet;
pub use packet::packet_search;

pub mod header;
pub use header::header_search;

#[tracing::instrument(skip(pool, rpc_client, rpc_addr, jsonrpc_req))]
pub async fn root(
    Extension(pool): Extension<PgPool>,
    Extension(rpc_client): Extension<HttpClient>,
    Extension(rpc_addr): Extension<Url>,
    jsonrpc_req: JsonRpc<serde_json::Value>,
) -> Result<Response, ReportError> {
    info!(?jsonrpc_req, "got request");

    let result = match Search::from_json_rpc(&jsonrpc_req) {
        Err(e) => {
            debug!("failed to parse tx search query from request: {}", e);

            return proxy(&rpc_client, &rpc_addr, jsonrpc_req).await;
        }
        Ok(Search::Tx(search)) => {
            debug!(?search, "got tx search request");

            tx_search(&pool, search).await
        }
        Ok(Search::Packet(search)) => {
            debug!(?search, "got packet request");

            packet_search(&pool, search).await
        }
        Ok(Search::Header(search)) => {
            debug!(?search, "got header request");

            header_search(&pool, search).await
        }
    };

    let response = match result {
        Ok(result) => jsonrpc_req.reply_success(result),
        Err(e) => {
            error!("failed to process tx search request: {}", e);
            jsonrpc_req.reply_error(e)
        }
    };

    Ok(response.into_response())
}
