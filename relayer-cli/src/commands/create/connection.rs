use abscissa_core::{Command, Options, Runnable};

use ibc::ics02_client::state::ClientState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::Height;
use ibc_relayer::config::StoreConfig;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::commands::cli_utils::{spawn_chain_runtime_memory, ChainHandlePair, SpawnOptions};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct CreateConnectionCommand {
    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, help = "identifier of the destination chain")]
    dst_chain_id: Option<ChainId>,

    #[options(help = "delay period parameter for the new connection", no_short)]
    delay: Option<u64>,

    #[options(
        help = "client identifier on the source chain; default: None (creates a new client)",
        no_short
    )]
    src_client: Option<ClientId>,

    #[options(
        help = "client identifier on the destination chain; default: None (creates a new client)",
        no_short
    )]
    dst_client: Option<ClientId>,
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
        if matches!(self.src_client, Some(_)) {
            return Output::error(
                "Option `<dst-chain-id>` is incompatible with `--src-client`".to_string(),
            )
            .exit();
        }
        if matches!(self.dst_client, Some(_)) {
            return Output::error(
                "Option `<dst-chain-id>` is incompatible with `--dst-client`".to_string(),
            )
            .exit();
        }

        info!(
            "Creating new client on chains {} and {}",
            self.src_chain_id, dst_chain_id
        );

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
        let config = app_config();

        // Validate & spawn runtime for the source chain.
        let src_chain = match spawn_chain_runtime_memory(&config, &self.src_chain_id) {
            Ok(handle) => handle,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        // Unwrap the identifier of the client on the source chain.
        let src_client_id = match &self.src_client {
            Some(c) => c,
            None => {
                return Output::error(
                    "Option `--src-client` is necessary when <dst-chain-id> is missing".to_string(),
                )
                .exit()
            }
        };

        // Verify that the client exists on the source chain, and fetch the chain_id that this client is verifying.
        let height = Height::new(src_chain.id().version(), 0);
        let dst_chain_id = match src_chain.query_client_state(&src_client_id, height) {
            Ok(cs) => cs.chain_id(),
            Err(e) => {
                return Output::error(format!(
                    "Failed while querying client {} on chain {} with error {}",
                    src_client_id, self.src_chain_id, e
                ))
                .exit()
            }
        };

        // Validate & spawn runtime for the destination chain.
        let dst_chain = match spawn_chain_runtime_memory(&config, &dst_chain_id) {
            Ok(handle) => handle,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        // Unwrap the identifier of the client on the destination chain.
        let dst_client_id = match &self.dst_client {
            Some(c) => c,
            None => {
                return Output::error(
                    "Option `--dst-client` is necessary when <dst-chain-id> is missing".to_string(),
                )
                .exit()
            }
        };

        info!(
            "Creating a new connection with pre-existing clients {} and {}",
            src_client_id, dst_client_id
        );

        // Create the two ForeignClient objects.
        let src_client = ForeignClient::find(src_chain.clone(), dst_chain.clone(), &src_client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);
        let dst_client = ForeignClient::find(dst_chain.clone(), src_chain.clone(), &dst_client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // All verification passed. Create the Connection object & do the handshake.
        let c = Connection::new(src_client, dst_client, self.delay);
    }
}
