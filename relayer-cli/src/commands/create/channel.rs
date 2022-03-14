use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::{ChainId, ConnectionId, PortId};
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::cli_utils::{spawn_chain_runtime, ChainHandlePair};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;
use ibc_relayer::config::default::connection_delay;

#[derive(Clone, Command, Debug, Parser)]
#[clap(disable_version_flag = true)]
pub struct CreateChannelCommand {
    #[clap(
        required = true,
        help = "identifier of the side `a` chain for the new channel"
    )]
    chain_a_id: ChainId,

    #[clap(help = "identifier of the side `b` chain for the new channel (optional)")]
    chain_b_id: Option<ChainId>,

    #[clap(
        short,
        long,
        help = "identifier of the connection on chain `a` to use in creating the new channel"
    )]
    connection_a: Option<ConnectionId>,

    #[clap(
        long,
        required = true,
        help = "identifier of the side `a` port for the new channel"
    )]
    port_a: PortId,

    #[clap(
        long,
        required = true,
        help = "identifier of the side `b` port for the new channel"
    )]
    port_b: PortId,

    #[clap(
        short,
        long,
        help = "the channel ordering, valid options 'unordered' (default) and 'ordered'",
        default_value_t
    )]
    order: Order,

    #[clap(
        short,
        long = "channel-version",
        alias = "version",
        help = "the version for the new channel"
    )]
    version: Option<String>,
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

        // Bail with an explicit error. The user might be expecting to use this connection.
        if self.connection_a.is_some() {
            Output::error(
                "Option `<connection-a>` is incompatible with `<chain-b-id>`".to_string(),
            )
            .exit();
        }

        let chains = ChainHandlePair::spawn(&config, &self.chain_a_id, chain_b_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        info!(
            "Creating new clients, new connection, and a new channel with order {}",
            self.order
        );

        let client_a = ForeignClient::new(chains.src.clone(), chains.dst.clone())
            .unwrap_or_else(exit_with_unrecoverable_error);
        let client_b = ForeignClient::new(chains.dst.clone(), chains.src)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Create the connection.
        let con = Connection::new(client_a, client_b, connection_delay())
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Finally create the channel.
        let channel = Channel::new(
            con,
            self.order,
            self.port_a.clone(),
            self.port_b.clone(),
            self.version.clone(),
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        Output::success(channel).exit();
    }

    // Creates a new channel, reusing an already existing connection and its clients.
    fn run_reusing_connection(&self) {
        let config = app_config();

        // Validate & spawn runtime for side a.
        let chain_a = spawn_chain_runtime(&config, &self.chain_a_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Unwrap the identifier of the connection on side a.
        let connection_a_id = match &self.connection_a {
            Some(c) => c,
            None => Output::error(
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
        let chain_b =
            spawn_chain_runtime(&config, &chain_b_id).unwrap_or_else(exit_with_unrecoverable_error);

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
            self.version.clone(),
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        Output::success(channel).exit();
    }
}
