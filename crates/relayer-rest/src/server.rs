use std::{
    error::Error,
    net::{
        SocketAddr,
        ToSocketAddrs,
    },
};

use axum::{
    extract::{
        Path,
        Query,
    },
    response::IntoResponse,
    routing::{
        get,
        post,
    },
    Extension,
    Json,
    Router,
    Server,
};
use crossbeam_channel as channel;
use ibc_relayer::rest::{
    request::Request,
    RestApiError,
};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use serde::{
    Deserialize,
    Serialize,
};
use tokio::task::JoinHandle;

use crate::handle::{
    all_chain_ids,
    assemble_version_info,
    chain_config,
    supervisor_state,
    trigger_clear_packets,
};

pub type BoxError = Box<dyn Error + Send + Sync>;

pub fn spawn(
    addr: impl ToSocketAddrs,
    sender: channel::Sender<Request>,
) -> Result<JoinHandle<()>, BoxError> {
    let addr = addr.to_socket_addrs()?.next().unwrap();
    let handle = tokio::spawn(run(addr, sender));
    Ok(handle)
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "status", content = "result")]
#[serde(rename_all = "lowercase")]
enum JsonResult<R, E> {
    Success(R),
    Error(E),
}

impl<R, E> From<Result<R, E>> for JsonResult<R, E> {
    fn from(r: Result<R, E>) -> Self {
        match r {
            Ok(a) => Self::Success(a),
            Err(e) => Self::Error(e),
        }
    }
}

async fn get_version(Extension(sender): Extension<Sender>) -> impl IntoResponse {
    let version: Result<_, RestApiError> = Ok(assemble_version_info(&sender));
    Json(JsonResult::from(version))
}

async fn get_chains(Extension(sender): Extension<Sender>) -> impl IntoResponse {
    let chain_ids = all_chain_ids(&sender);
    Json(JsonResult::from(chain_ids))
}

async fn get_chain(
    Path(id): Path<String>,
    Extension(sender): Extension<Sender>,
) -> impl IntoResponse {
    let chain = chain_config(&sender, &id);
    Json(JsonResult::from(chain))
}

async fn get_state(Extension(sender): Extension<Sender>) -> impl IntoResponse {
    let state = supervisor_state(&sender);
    Json(JsonResult::from(state))
}

#[derive(Debug, Deserialize)]
struct ClearPacketParams {
    chain: Option<ChainId>,
}

async fn clear_packets(
    Extension(sender): Extension<Sender>,
    Query(params): Query<ClearPacketParams>,
) -> impl IntoResponse {
    let result = trigger_clear_packets(&sender, params.chain);
    Json(JsonResult::from(result))
}

type Sender = channel::Sender<Request>;

async fn run(addr: SocketAddr, sender: Sender) {
    let app = Router::new()
        .route("/version", get(get_version))
        .route("/chains", get(get_chains))
        .route("/chain/:id", get(get_chain))
        .route("/state", get(get_state))
        .route("/clear_packets", post(clear_packets))
        .layer(Extension(sender));

    Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
