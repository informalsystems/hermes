use std::thread;

use crossbeam_channel as channel;
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

    info!("[rest] starting REST API server at {}", config.address);
    let handle = run(config, req_tx);

    (handle, req_rx)
}

#[allow(clippy::manual_strip)]
fn run(config: Config, sender: channel::Sender<Request>) -> ServerHandle {
    let server = rouille::Server::new(config.address, move |request| {
        router!(request,
            (GET) (/) => {
                trace!("[rest/server] GET /");
                let result = assemble_version_info(&sender);
                rouille::Response::json(&result)
            },

            (GET) (/chain) => {
                // TODO(Soares): Add a `into_detail` to consume the error and obtain
                //   the underlying detail, so that we avoid doing `e.0`
                trace!("[rest/server] GET /chain");
                rouille::Response::json(&all_chain_ids(&sender).map_err(|e| e.0))
            },

            (GET) (/chain/{id: String}) => {
                trace!("[rest/server] GET /chain/{}", id);
                rouille::Response::json(&chain_config(&sender, &id).map_err(|e| e.0))
            },

            (GET) (/state) => {
                trace!("[rest/server] GET /state");
                rouille::Response::json(&supervisor_state(&sender).map_err(|e| e.0))
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
