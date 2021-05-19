use crate::config::Config;
use crossbeam_channel as channel;
use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::config::ChainConfig;
use ibc_relayer::{
    error::{Error, Kind},
    rest::{reply_channel, ReplyTo, Request},
};
use serde::Serialize;
use std::str::FromStr;
use std::{fmt::Debug, thread};
use tracing::info;

#[derive(Serialize)]
struct PrintableError {
    error: String,
}

impl PrintableError {
    pub fn new(e: Error) -> Self {
        Self {
            error: e.to_string(),
        }
    }
}

pub fn spawn(config: Config) -> (thread::JoinHandle<()>, channel::Receiver<Request>) {
    let (request_sender, request_receiver) = channel::unbounded::<Request>();
    info!("starting REST API server at {}", config.connection);
    (
        thread::spawn(move || run(config, request_sender)),
        request_receiver,
    )
}

fn send<F, O>(sender: &channel::Sender<Request>, f: F) -> Result<O, Error>
where
    F: FnOnce(ReplyTo<O>) -> Request,
    O: Debug,
{
    let (reply_sender, reply_receiver) = reply_channel();
    let input = f(reply_sender);

    sender.send(input).map_err(Kind::channel)?;

    reply_receiver.recv().map_err(Kind::channel)?
}

#[allow(clippy::manual_strip)]
fn run(config: Config, sender: channel::Sender<Request>) {
    rouille::start_server(config.connection, move |request| {
        router!(request,
            (GET) (/) => {
                let result = send(&sender, |reply_to| Request::Version { reply_to }).unwrap();
                rouille::Response::json(&result)
            },

            (GET) (/chain) => {
                let result = send(&sender, |reply_to| Request::GetChains { reply_to }).unwrap();
                rouille::Response::json(&result)
            },

            (GET) (/chain/{id: String}) => {
                match ChainId::from_str(&id) {
                    Ok(chain_id) => {
                        match send(&sender, |reply_to| Request::GetChain { chain_id, reply_to }) {
                            Ok(chain_config) => rouille::Response::json(&chain_config),
                            Err(e) => rouille::Response::json(&PrintableError::new(e)),
                        }
                    },
                    Err(e) => {
                        rouille::Response::json(&PrintableError::new(Kind::ChainIdentifier(id).context(e).into()))
                    }
                }
            },

            (POST) (/chain) => {
                let chain_config: ChainConfig = try_or_400!(rouille::input::json_input(&request));
                match send(&sender, |reply_to| Request::AddChain { chain_config, reply_to }) {
                    Ok(result) => rouille::Response::json(&result),
                    Err(e) => rouille::Response::json(&PrintableError::new(e)),
                }
            },

            _ => rouille::Response::empty_404(),
        )
    });
}
