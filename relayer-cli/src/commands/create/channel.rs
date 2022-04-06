use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use console::style;
use dialoguer::Confirm;

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics04_channel::Version;
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

static PROMPT: &str = "Are you sure you want a new connection & clients to be created? Hermes will use default security parameters.";
static HINT: &str = "Consider using the default invocation\n\nhermes create channel --port-a <PORT-ID> --port-b <PORT-ID> <CHAIN-A-ID> <CONNECTION-A-ID>\n\nto re-use a pre-existing connection.";

/// The data structure that represents all the possible options when invoking
/// the `create channel` CLI command.
///
/// There are two possible ways to invoke this command:
///
/// `create channel --port-a <Port-ID> --port-b <Port-ID> <Chain-A-ID> <Connection-ID>` is the default
/// way in which this command should be used, specifying a `Connection-ID` for this new channel
/// to re-use. The command expects that `Connection-ID` is associated with chain A.
///
/// `create channel --port-a <Port-ID> --port-b <Port-ID> <Chain-A-ID> <Chain-B-ID> --new-client-connection`
/// to indicate that a new connection/client pair is being created as part of this new channel.
/// This brings up an interactive yes/no prompt to ensure that the operator at least
/// considers the fact that they're initializing a new connection with the channel.
///
/// Note that `Connection-ID`s have to be considered based off of the chain's perspective. Although
/// chain A and chain B might refer to the connection with different names, they are actually referring
/// to the same connection.
#[derive(Clone, Command, Debug, Parser)]
#[clap(disable_version_flag = true)]
pub struct CreateChannelCommand {
    #[clap(
        required = true,
        help = "Identifier of the side `a` chain for the new channel"
    )]
    chain_a: ChainId,

    #[clap(
        short,
        long,
        help = "Identifier of the side `b` chain for the new channel"
    )]
    chain_b: Option<ChainId>,

    /// Identifier of the connection on chain `a` to use in creating the new channel.
    connection_a: Option<ConnectionId>,

    #[clap(
        long,
        required = true,
        help = "Identifier of the side `a` port for the new channel"
    )]
    port_a: PortId,

    #[clap(
        long,
        required = true,
        help = "Identifier of the side `b` port for the new channel"
    )]
    port_b: PortId,

    #[clap(
        short,
        long,
        help = "The channel ordering, valid options 'unordered' (default) and 'ordered'",
        default_value_t
    )]
    order: Order,

    #[clap(
        short,
        long = "channel-version",
        alias = "version",
        help = "The version for the new channel"
    )]
    version: Option<Version>,

    #[clap(
        long,
        help = "Indicates that a new client and connection will be created underlying the new channel"
    )]
    new_client_connection: bool,
}

impl Runnable for CreateChannelCommand {
    fn run(&self) {
        match &self.connection_a {
            Some(conn) => self.run_reusing_connection(conn),
            None => match &self.chain_b {
                Some(chain_b) => {
                    if self.new_client_connection {
                        match Confirm::new()
                            .with_prompt(format!(
                                "{}: {}\n{}: {}",
                                style("WARN").yellow(),
                                PROMPT,
                                style("Hint").cyan(),
                                HINT
                            ))
                            .interact()
                        {
                            Ok(confirm) => {
                                if confirm {
                                    self.run_using_new_connection(chain_b);
                                } else {
                                    Output::error("You elected not to create new clients and connections. Please re-invoke `create channel` with a pre-existing connection ID".to_string()).exit();
                                }
                            }
                            Err(e) => {
                                Output::error(format!(
                                    "An error occurred while waiting for user input: {}",
                                    e
                                ));
                            }
                        }
                    } else {
                        Output::error(
                                "The `--new-client-connection` flag is required if invoking with `--chain-b`".to_string()
                            )
                            .exit();
                    }
                }
                None => Output::error("Missing one of `<chain-b>` or `<connection-a>`".to_string())
                    .exit(),
            },
        }
    }
}

impl CreateChannelCommand {
    /// Creates a new channel, as well as a new underlying connection and clients.
    fn run_using_new_connection(&self, chain_b: &ChainId) {
        let config = app_config();

        let chains = ChainHandlePair::spawn(&config, &self.chain_a, chain_b)
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

    /// Creates a new channel, reusing an already existing connection and its clients.
    fn run_reusing_connection(&self, connection_a: &ConnectionId) {
        let config = app_config();

        // Validate & spawn runtime for side a.
        let chain_a = spawn_chain_runtime(&config, &self.chain_a)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Query the connection end.
        let height = Height::new(chain_a.id().version(), 0);
        let conn_end = chain_a
            .query_connection(connection_a, height)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Query the client state, obtain the identifier of chain b.
        let chain_b = chain_a
            .query_client_state(conn_end.client_id(), height)
            .map(|cs| cs.chain_id())
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Spawn the runtime for side b.
        let chain_b =
            spawn_chain_runtime(&config, &chain_b).unwrap_or_else(exit_with_unrecoverable_error);

        // Create the foreign client handles.
        let client_a = ForeignClient::find(chain_b.clone(), chain_a.clone(), conn_end.client_id())
            .unwrap_or_else(exit_with_unrecoverable_error);
        let client_b = ForeignClient::find(chain_a, chain_b, conn_end.counterparty().client_id())
            .unwrap_or_else(exit_with_unrecoverable_error);

        let identified_end = IdentifiedConnectionEnd::new(connection_a.clone(), conn_end);

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
