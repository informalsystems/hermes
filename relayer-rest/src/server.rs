use std::thread;

use crossbeam_channel as channel;
use serde::{Deserialize, Serialize};
use tracing::{info, trace};

use ibc_relayer::rest::request::Request;

use crate::{
    handle::{all_chain_ids, assemble_version_info, chain_config, supervisor_state},
    Config,
};

pub struct ServerHandle {
    join_handle: thread::JoinHandle<()>,
    tx_stop: std::sync::mpsc::Sender<()>,
}

impl ServerHandle {
    pub fn join(self) -> std::thread::Result<()> {
        self.join_handle.join()
    }

    pub fn stop(&self) {
        self.tx_stop.send(()).unwrap();
    }
}

pub fn spawn(config: Config) -> (ServerHandle, channel::Receiver<Request>) {
    let (req_tx, req_rx) = channel::unbounded::<Request>();

    info!("starting REST API server listening at http://{}", config);
    let handle = run(config, req_tx);

    (handle, req_rx)
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

#[allow(clippy::manual_strip)]
fn run(config: Config, sender: channel::Sender<Request>) -> ServerHandle {
    let server = rouille::Server::new(config.address(), move |request| {
        router!(request,
            (GET) (/version) => {
                trace!("[rest/server] GET /version");
                let result = assemble_version_info(&sender);
                rouille::Response::json(&result)
            },

            (GET) (/chains) => {
                // TODO(Soares): Add a `into_detail` to consume the error and obtain
                //   the underlying detail, so that we avoid doing `e.0`
                trace!("[rest] GET /chains");
                let result = all_chain_ids(&sender);
                rouille::Response::json(&JsonResult::from(result))
            },

            (GET) (/chain/{id: String}) => {
                trace!("[rest] GET /chain/{}", id);
                let result = chain_config(&sender, &id);
                rouille::Response::json(&JsonResult::from(result))
            },

            (GET) (/state) => {
                trace!("[rest] GET /state");
                let result = supervisor_state(&sender);
                rouille::Response::json(&JsonResult::from(result))
            },

            _ => rouille::Response::empty_404(),
        )
    })
    .unwrap();

    let (join_handle, tx_stop) = server.stoppable();

    ServerHandle {
        join_handle,
        tx_stop,
    }
}
