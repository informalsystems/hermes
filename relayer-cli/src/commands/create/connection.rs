use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::config::StoreConfig;

use crate::commands::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::Output;
use crate::prelude::*;
use ibc_relayer::foreign_client::ForeignClient;

#[derive(Clone, Command, Debug, Options)]
pub struct CreateConnectionCommand {
    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    // TODO: document the default value in the help output? use constant.
    #[options(
        help = "delay period parameter for the new connection",
        short = "d"
    )]
    delay: Option<u64>,

    #[options(
        help = "client identifier on the source chain; default: None (new client is created) "
    )]
    src_client_id: Option<ClientId>,

    #[options(
        help = "client identifier on the destination chain; default: None (new client is created) "
    )]
    dst_client_id: Option<ClientId>,
}

// cargo run --bin hermes -- create connection ibc-0 ibc-1
// cargo run --bin hermes -- create connection ibc-0 ibc-1 --delay 1000
// cargo run --bin hermes -- create connection ibc-0 --src-client-id 07-tendermint-0 --dst-client-id 07-tendermint-0 [--delay <delay>]
impl Runnable for CreateConnectionCommand {
    fn run(&self) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());
        let chains = match ChainHandlePair::spawn_with(
            spawn_options,
            &config,
            &self.src_chain_id,
            &self.dst_chain_id,
        ) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        match self.src_client_id.clone() {
            None => {
                // Create a foreign client.
                let client = ForeignClient::new(chains.dst, chains.src);
            }
            Some(expected_client_id) => {
                // Find and validate the client.
                let client = ForeignClient::find(chains.dst, chains.src, expected_client_id);
            }
        }
    }
}
