use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::config::StoreConfig;

use crate::commands::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::exit_with_unrecoverable_error;
use crate::prelude::*;
use ibc_relayer::foreign_client::ForeignClient;

#[derive(Clone, Command, Debug, Options)]
pub struct CreateConnectionCommand {
    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    // TODO: document the default value in the help output? use constant.
    #[options(help = "delay period parameter for the new connection", short = "d")]
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
        let chains = ChainHandlePair::spawn_with(
            spawn_options,
            &config,
            &self.src_chain_id,
            &self.dst_chain_id,
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        // Find or create the client on the source chain.
        let src_client = match self.src_client_id.clone() {
            None => {
                // Create a foreign client.
                ForeignClient::new(chains.src.clone(), chains.dst.clone())
                    .unwrap_or_else(exit_with_unrecoverable_error)
            }
            Some(expected_src_client_id) => {
                // Find and validate the client.
                ForeignClient::find(
                    chains.src.clone(),
                    chains.dst.clone(),
                    expected_src_client_id,
                )
                .unwrap_or_else(exit_with_unrecoverable_error)
            }
        };

        // Find or create the client on the destination chain.
        let dst_client = match self.dst_client_id.clone() {
            None => ForeignClient::new(chains.dst.clone(), chains.src.clone())
                .unwrap_or_else(exit_with_unrecoverable_error),
            Some(expected_dst_client_id) => ForeignClient::find(
                chains.dst.clone(),
                chains.src.clone(),
                expected_dst_client_id,
            )
            .unwrap_or_else(exit_with_unrecoverable_error),
        };
    }
}
