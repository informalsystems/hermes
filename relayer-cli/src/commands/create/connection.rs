use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::config::StoreConfig;
use ibc_relayer::foreign_client::ForeignClient;

use crate::commands::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;
use ibc_relayer::connection::Connection;

#[derive(Clone, Command, Debug, Options)]
pub struct CreateConnectionCommand {
    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, help = "identifier of the destination chain")]
    dst_chain_id: Option<ChainId>,

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
        match &self.dst_chain_id {
            Some(dst_chain_id) => self.create_from_scratch(dst_chain_id),
            None => self.create_reusing_clients(),
        }
    }
}

impl CreateConnectionCommand {
    /// Create a connection with new clients.
    fn create_from_scratch(&self, dst_chain_id: &ChainId) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());

        let chains =
            ChainHandlePair::spawn_with(spawn_options, &config, &self.src_chain_id, dst_chain_id)
                .unwrap_or_else(exit_with_unrecoverable_error);

        // Validate the other options. Bail if the CLI was invoked with incompatible options.
        if matches!(self.src_client_id, Some(_)) {
            return Output::error(
                "Option `<dst-chain-id>` is incompatible with `--src-client-id`".to_string(),
            )
            .exit();
        }
        if matches!(self.dst_client_id, Some(_)) {
            return Output::error(
                "Option `<dst-chain-id>` is incompatible with `--dst-client-id`".to_string(),
            )
            .exit();
        }

        // Create the two clients.
        let src_client = ForeignClient::new(chains.src.clone(), chains.dst.clone())
            .unwrap_or_else(exit_with_unrecoverable_error);
        let dst_client = ForeignClient::new(chains.dst.clone(), chains.src.clone())
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Now execute the connection handshake.
        let c = Connection::new(src_client, dst_client, self.delay);
    }

    /// Create a connection reusing pre-existing clients on both chains.
    fn create_reusing_clients(&self) {
        // let config = app_config();

        // let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());

        // Validate the client options.
        let src_client = match &self.src_client_id {
            None => Output::error(
                "Option `--src-client-id` is necessary when <dst-chain-id> is missing".to_string(),
            )
            .exit(),
            Some(expected_src_client_id) => {
                // TODO(Adi) Modify the `find` method.
                // ForeignClient::find(
                //     chains.src.clone(),
                //     chains.dst.clone(),
                //     expected_src_client_id,
                // )
                //     .unwrap_or_else(exit_with_unrecoverable_error)
            }
        };

        match &self.dst_client_id {
            None => Output::error(
                "Option `--dst-client-id` is necessary when <dst-chain-id> is missing".to_string(),
            )
            .exit(),
            Some(dst_client_id) => {
                unimplemented!()
            }
        }
    }
}
