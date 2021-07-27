use std::thread;

use crossbeam_channel as channel;
use tracing::{info, trace};

use ibc_relayer::rest::request::Request;

use crate::{
    handle::{add_chain, all_chain_ids, assemble_version_info, chain_config, supervisor_state},
    Config,
};

pub fn spawn(config: Config) -> (thread::JoinHandle<()>, channel::Receiver<Request>) {
    let (request_sender, request_receiver) = channel::unbounded::<Request>();
    info!("[rest] starting REST API server at {}", config.address);
    (
        thread::spawn(move || run(config, request_sender)),
        request_receiver,
    )
}

// TODO(Adi): remove unwraps, or double-check that `rouille` can recover from panics
#[allow(clippy::manual_strip)]
fn run(config: Config, sender: channel::Sender<Request>) {
    rouille::start_server(config.address, move |request| {
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

            (POST) (/chain) => {
                trace!("[rest/server] POST /chain");
                rouille::Response::json(&add_chain(&sender, request).map_err(|e| e.0))
            },

            _ => rouille::Response::empty_404(),
        )
    });
}
