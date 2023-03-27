use std::{
    error::Error,
    net::{SocketAddr, ToSocketAddrs},
};

use axum::{extract::Path, response::IntoResponse, routing::get, Extension, Json, Router, Server};
use crossbeam_channel as channel;
use serde::{Deserialize, Serialize};
use tokio::task::JoinHandle;

use ibc_relayer::{
    rest::{request::Request, RestApiError},
    supervisor::dump_state::SupervisorState,
};

use crate::handle::{all_chain_ids, assemble_version_info, chain_config, supervisor_state};

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

async fn get_state(
    Extension(sender): Extension<Sender>,
) -> Json<JsonResult<SupervisorState, RestApiError>> {
    let state = supervisor_state(&sender);
    Json(JsonResult::from(state))
}

type Sender = channel::Sender<Request>;

async fn run(addr: SocketAddr, sender: Sender) {
    let app = Router::new()
        .route("/version", get(get_version))
        .route("/chains", get(get_chains))
        .route("/chain/:id", get(get_chain))
        .route("/state", get(get_state))
        .layer(Extension(sender));

    Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
