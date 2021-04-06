use abscissa_core::{Command, Options, Runnable};

use ibc::ics02_client::client_state::ClientState;
use ibc::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChainId, ConnectionId, PortId};
use ibc::Height;
use ibc_relayer::channel::Channel;
use ibc_relayer::config::StoreConfig;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::cli_utils::{spawn_chain_runtime, ChainHandlePair, SpawnOptions};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct CreateChannelCommand {
    #[options(
        free,
        required,
        help = "identifier of the side `a` chain for the new channel"
    )]
    chain_a_id: ChainId,

    #[options(
        free,
        help = "identifier of the side `b` chain for the new channel (optional)"
    )]
    chain_b_id: Option<ChainId>,

    #[options(
        help = "identifier of the connection on chain `a` to use in creating the new channel"
    )]
    connection_a: Option<ConnectionId>,

    #[options(
        no_short,
        required,
        help = "identifier of the side `a` port for the new channel"
    )]
    port_a: PortId,

    #[options(
        no_short,
        required,
        help = "identifier of the side `b` port for the new channel"
    )]
    port_b: PortId,

    #[options(help = "the order for parametrizing the new channel")]
    order: Order,

    #[options(help = "the version for parametrizing the new channel")]
    version: String,
}

impl Runnable for CreateChannelCommand {
    fn run(&self) {
        match &self.chain_b_id {
            None => self.run_reusing_connection(),
            Some(chain_b) => self.run_using_new_connection(chain_b),
        }
    }
}

impl CreateChannelCommand {
    // Creates a new channel, as well as a new underlying connection and clients.
    fn run_using_new_connection(&self, chain_b_id: &ChainId) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());

        let chains =
            ChainHandlePair::spawn_with(spawn_options, &config, &self.chain_a_id, chain_b_id)
                .unwrap_or_else(exit_with_unrecoverable_error);
        info!(
            "Creating new clients, new connection, and a new channel with order {:?} and version {}",
            self.order, self.version
        );

        let client_a = ForeignClient::new(chains.src.clone(), chains.dst.clone())
            .unwrap_or_else(exit_with_unrecoverable_error);
        let client_b = ForeignClient::new(chains.dst.clone(), chains.src.clone())
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Create the connection.
        // TODO: pass the `delay` parameter here.
        let con =
            Connection::new(client_a, client_b, 0).unwrap_or_else(exit_with_unrecoverable_error);

        // Finally create the channel.
        let channel = Channel::new(con, self.order, self.port_a.clone(), self.port_b.clone())
            .unwrap_or_else(exit_with_unrecoverable_error);

        Output::success(channel).exit();
    }

    // Creates a new channel, reusing an already existing connection and its clients.
    fn run_reusing_connection(&self) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());

        // Validate & spawn runtime for side a.
        let chain_a = spawn_chain_runtime(spawn_options.clone(), &config, &self.chain_a_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Unwrap the identifier of the connection on side a.
        let connection_a_id =
            match &self.connection_a {
                Some(c) => c,
                None => return Output::error(
                    "Option `--connection-a` is necessary when <chain-b-id> argument is missing"
                        .to_string(),
                )
                .exit(),
            };

        // Query the connection end.
        let height = Height::new(chain_a.id().version(), 0);
        let conn_end = chain_a
            .query_connection(connection_a_id, height)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Query the client state, obtain the identifier of chain b.
        let chain_b_id = chain_a
            .query_client_state(conn_end.client_id(), height)
            .map(|cs| cs.chain_id())
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Spawn the runtime for side b.
        let chain_b = spawn_chain_runtime(spawn_options, &config, &chain_b_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Create the foreign client handles.
        let client_a = ForeignClient::find(chain_b.clone(), chain_a.clone(), conn_end.client_id())
            .unwrap_or_else(exit_with_unrecoverable_error);
        let client_b = ForeignClient::find(chain_a, chain_b, conn_end.counterparty().client_id())
            .unwrap_or_else(exit_with_unrecoverable_error);

        let identified_end = IdentifiedConnectionEnd::new(connection_a_id.clone(), conn_end);

        let connection = Connection::find(client_a, client_b, &identified_end)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let channel = Channel::new(
            connection,
            self.order,
            self.port_a.clone(),
            self.port_b.clone(),
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        Output::success(channel).exit();
    }
}
