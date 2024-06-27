use abscissa_core::clap::Parser;

use console::style;
use dialoguer::Confirm;

use crate::cli_utils::{spawn_chain_runtime, ChainHandlePair};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;
use crate::prelude::*;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, QueryClientStateRequest, QueryConnectionRequest, QueryHeight,
};
use ibc_relayer::channel::Channel;
use ibc_relayer::config::default::connection_delay;
use ibc_relayer::connection::{Connection, ConnectionError};
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer_types::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc_relayer_types::core::ics04_channel::channel::Ordering;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ConnectionId, ConnectionIds, PortId,
};
use ibc_relayer_types::core::ics33_multihop::channel_path::ConnectionHop;

static PROMPT: &str = "Are you sure you want a new connection & clients to be created? Hermes will use default security parameters.";
static HINT: &str = "Consider using the default invocation\n\nhermes create channel --a-port <PORT-ID> --b-port <PORT-ID> --a-chain <CHAIN-A-ID> --a-connection <CONNECTION-A-ID>\n\nto reuse a pre-existing connection.";

/// The data structure that represents all the possible options when invoking
/// the `create channel` CLI command.
///
/// There are two possible ways to invoke this command:
///
/// `create channel --a-port <A_PORT_ID> --b-port <B_PORT_ID> --a-chain <A_CHAIN_ID> --a-connection <A_CONNECTION_ID>`
/// is the default way in which this command should be used, specifying a `Connection-ID`
/// associated with chain A for this new channel to reuse.
///
/// `create channel --a-port <A_PORT_ID> --b-port <B_PORT_ID> --a-chain <A_CHAIN_ID> --b-chain <B_CHAIN_ID> --new-client-connection`
/// can alternatively be used to indicate that a new connection/client pair is being
/// created as part of this new channel. This brings up an interactive yes/no prompt
/// to ensure that the operator at least considers the fact that they're initializing a
/// new connection with the channel. This prompt can be skipped by appending the `--yes`
/// flag to the command.
///
/// Note that `Connection-ID`s have to be considered based off of the chain's perspective. Although
/// chain A and chain B might refer to the connection with different names, they are actually referring
/// to the same connection.
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
#[clap(override_usage = "
    hermes create channel [OPTIONS] --a-chain <A_CHAIN_ID> --a-connection <A_CONNECTION_ID> --a-port <A_PORT_ID> --b-port <B_PORT_ID>

    hermes create channel [OPTIONS] --a-chain <A_CHAIN_ID> --a-connection <A_CONNECTION_ID> --connection-hops <CONNECTION_HOP_IDS> --a-port <A_PORT_ID> --b-port <B_PORT_ID>

    hermes create channel [OPTIONS] --a-chain <A_CHAIN_ID> --b-chain <B_CHAIN_ID> --a-port <A_PORT_ID> --b-port <B_PORT_ID> --new-client-connection

    NOTE: The `--new-client-connection` option does not support connection hops. To open a multi-hop channel, please provide existing connections or initialize them manually before invoking this command.
    ")]
pub struct CreateChannelCommand {
    #[clap(
        long = "a-chain",
        required = true,
        value_name = "A_CHAIN_ID",
        help_heading = "FLAGS",
        help = "Identifier of the side `a` chain for the new channel"
    )]
    chain_a: ChainId,

    #[clap(
        long = "b-chain",
        value_name = "B_CHAIN_ID",
        required = true,
        requires = "new-client-connection",
        group = "b_chain_group",
        help_heading = "FLAGS",
        help = "Identifier of the side `b` chain for the new channel"
    )]
    chain_b: Option<ChainId>,

    #[clap(
        long = "a-connection",
        visible_alias = "a-conn",
        value_name = "A_CONNECTION_ID",
        required = true,
        groups = &["b_chain_group", "new_client_group"],
        help_heading = "FLAGS",
        help = "Identifier of the connection on chain `a` to use in creating the new channel"
    )]
    connection_a: Option<ConnectionId>,

    #[clap(
        long = "a-port",
        required = true,
        value_name = "A_PORT_ID",
        help_heading = "FLAGS",
        help = "Identifier of the side `a` port for the new channel"
    )]
    port_a: PortId,

    #[clap(
        long = "b-port",
        required = true,
        value_name = "B_PORT_ID",
        help_heading = "FLAGS",
        help = "Identifier of the side `b` port for the new channel"
    )]
    port_b: PortId,

    #[clap(
        long = "order",
        value_name = "ORDER",
        help = "The channel ordering, valid options 'unordered' (default) and 'ordered'",
        default_value_t
    )]
    order: Ordering,

    #[clap(
        long = "channel-version",
        visible_alias = "chan-version",
        value_name = "VERSION",
        help = "The version for the new channel"
    )]
    version: Option<Version>,

    #[clap(
        long = "new-client-connection",
        visible_alias = "new-client-conn",
        required = true,
        group = "new_client_group",
        help = "Indicates that a new client and connection will be created underlying the new channel"
    )]
    new_client_connection: bool,

    #[clap(
        long = "yes",
        requires = "new-client-connection",
        help = "Skip new_client_connection confirmation"
    )]
    yes: bool,

    // --connection-hops receives a list of ConnectionId of intermediate connections between two chains
    // if they are to be connected via a multihop channel. The list of connection identifiers passed to
    // `--connection-hops` starts with the identifier of the connection that comes after `--a-connection`
    // in the channel path from `--a-chain` towards `--b-chain`. For example, given the following
    // channel path, where `--a-chain` is Chain-A and `--b-chain` is Chain-D:
    //
    //  +---------+    connection-1   +---------+    connection-2   +---------+    connection-3   +---------+
    //  | Chain-A | ----------------> | Chain-B | ----------------> | Chain-C | ----------------> | Chain-D |
    //  +---------+                   +---------+                   +---------+                   +---------+
    //
    // The --connection-hops parameter should receive 'connection-2/connection-3' as argument.
    #[clap(
        long = "connection-hops",
        visible_alias = "conn-hops",
        value_name = "CONNECTION_HOP_IDS",
        required = true,
        requires = "connection-a",
        conflicts_with_all = &["new-client-connection", "chain-b"],
        help_heading = "FLAGS",
        help = "A list of identifiers of the intermediate connections between \
        side `a` and side `b` for a multi-hop channel, separated by slashes, \
        e.g, 'connection-1/connection-0' (optional)."
    )]
    connection_hops: Option<ConnectionIds>,
}

impl Runnable for CreateChannelCommand {
    fn run(&self) {
        match &self.connection_a {
            Some(conn) => {
                if let Some(conn_hops) = &self.connection_hops {
                    self.run_multihop_reusing_connection(conn, conn_hops);
                } else {
                    self.run_reusing_connection(conn);
                }
            }
            None => {
                if let Some(chain_b) = &self.chain_b {
                    if self.new_client_connection {
                        if self.yes {
                            self.run_using_new_connection(chain_b);
                        } else {
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
                                        "An error occurred while waiting for user input: {e}"
                                    ));
                                }
                            }
                        }
                    }
                }
            }
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
            None,
            None,
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
        let (conn_end, _) = chain_a
            .query_connection(
                QueryConnectionRequest {
                    connection_id: connection_a.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .unwrap_or_else(exit_with_unrecoverable_error);

        // Query the client state, obtain the identifier of chain b.
        let chain_b = chain_a
            .query_client_state(
                QueryClientStateRequest {
                    client_id: conn_end.client_id().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(cs, _)| cs.chain_id())
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
            None,
            None,
            self.version.clone(),
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        Output::success(channel).exit();
    }

    /// Creates a new multi-hop channel, reusing existing connections as the channel path.
    fn run_multihop_reusing_connection(
        &self,
        connection_a: &ConnectionId,
        connection_hops: &ConnectionIds,
    ) {
        let config = app_config();

        let mut a_side_hops = Vec::new(); // Hops from --a-side towards --b-side
        let mut b_side_hops = Vec::new(); // Hops from --b-side towards --a-side

        // Join `connection_a` and `connection_hops` to create a Vec containing the identifiers
        // of the connections that form the channel path from `--a-side` to `--b-side`
        let mut conn_hop_ids = connection_hops.clone().into_vec();
        conn_hop_ids.insert(0, connection_a.clone());

        // The identifier of the chain from which we will start constructing the connection hops.
        let mut chain_id = self.chain_a.clone();

        // Iterate through the list of connection hop identifiers that constitute the
        // channel path from `--a-chain` towards `--b-chain`.
        for a_side_connection_id in conn_hop_ids.iter() {
            let chain_handle = match spawn_chain_runtime(&config, &chain_id) {
                Ok(handle) => handle,
                Err(e) => Output::error(e).exit(),
            };

            let a_side_hop_connection = match chain_handle.query_connection(
                QueryConnectionRequest {
                    connection_id: a_side_connection_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            ) {
                Ok((connection, _)) => connection,
                Err(e) => Output::error(e).exit(),
            };

            let a_side_hop_conn_client_state = match chain_handle.query_client_state(
                QueryClientStateRequest {
                    client_id: a_side_hop_connection.client_id().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            ) {
                Ok((client_state, _)) => client_state,
                Err(e) => Output::error(e).exit(),
            };

            // Obtain the counterparty ConnectionId and ChainId for the current connection hop
            // towards b_side
            let counterparty_conn_id = a_side_hop_connection
                .counterparty()
                .connection_id()
                .unwrap_or_else(|| {
                    Output::error(ConnectionError::missing_counterparty_connection_id()).exit()
                });

            let counterparty_chain_id = a_side_hop_conn_client_state.chain_id().clone();

            let counterparty_handle = match spawn_chain_runtime(&config, &counterparty_chain_id) {
                Ok(handle) => handle,
                Err(e) => Output::error(e).exit(),
            };

            // Retrieve the counterparty connection
            let counterparty_connection = match counterparty_handle.query_connection(
                QueryConnectionRequest {
                    connection_id: counterparty_conn_id.clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            ) {
                Ok((connection, _)) => connection,
                Err(e) => Output::error(e).exit(),
            };

            a_side_hops.push(ConnectionHop {
                connection: IdentifiedConnectionEnd::new(
                    a_side_connection_id.clone(),
                    a_side_hop_connection.clone(),
                ),
                src_chain_id: chain_id.clone(),
                dst_chain_id: a_side_hop_conn_client_state.chain_id(),
            });

            // Build the current hop from the opposite direction
            b_side_hops.push(ConnectionHop {
                connection: IdentifiedConnectionEnd::new(
                    counterparty_conn_id.clone(),
                    counterparty_connection,
                ),
                src_chain_id: a_side_hop_conn_client_state.chain_id(),
                dst_chain_id: chain_id.clone(),
            });

            // Update chain_id to point to the next chain in the channel path
            // from a_side towards b_side
            chain_id = a_side_hop_conn_client_state.chain_id().clone();
        }

        // Ensure that the final chain in the path, stored in chain_id, is not the same chain as
        // `--a-chain`, i.e, check that the connection hops do not lead back to `--a-chain`.
        if chain_id == self.chain_a {
            Output::error(Error::ics33_hops_return_to_source(
                connection_hops.clone(),
                self.chain_a.clone(),
            ))
            .exit()
        }

        let a_chain = match spawn_chain_runtime(&config, &self.chain_a) {
            Ok(handle) => handle,
            Err(e) => Output::error(e).exit(),
        };

        let b_chain = match spawn_chain_runtime(&config, &chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(e).exit(),
        };

        // The connection hops were assembled while traversing from --a-chain towards --b-chain.
        // Reverse b_side_hops to to obtain the correct path from --b-chain to --a-chain.
        b_side_hops.reverse();

        // The first connection from a_side towards b_side
        let a_side_connection = a_side_hops
            .first()
            .expect("a_side hops is never empty")
            .connection
            .clone();

        // The first connection from b_side towards a_side
        let b_side_connection = b_side_hops
            .first()
            .expect("b_side hops is never empty")
            .connection
            .clone();

        let channel = Channel::new_multihop(
            a_chain,
            b_chain,
            a_side_connection,
            b_side_connection,
            self.order,
            self.port_a.clone(),
            self.port_b.clone(),
            None, // FIXME: Unsure about what to add here ('None' for now)
            None, // FIXME: Unsure about what to add here ('None' for now)
            self.version.clone(),
            core::time::Duration::from_secs(0), // FIXME: We need to figure out how to determine the connection delay for multi-hop channels
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        Output::success(channel).exit();
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::CreateChannelCommand;
    use abscissa_core::clap::Parser;

    use ibc_relayer_types::core::ics04_channel::channel::Ordering;
    use ibc_relayer_types::core::ics04_channel::version::Version;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ConnectionId, PortId};

    #[test]
    fn test_create_channel_a_conn_required() {
        assert_eq!(
            CreateChannelCommand {
                chain_a: ChainId::from_string("chain_a"),
                chain_b: None,
                connection_a: Some(ConnectionId::from_str("connection_a").unwrap()),
                connection_hops: None,
                port_a: PortId::from_str("port_id_a").unwrap(),
                port_b: PortId::from_str("port_id_b").unwrap(),
                order: Ordering::Unordered,
                version: None,
                new_client_connection: false,
                yes: false
            },
            CreateChannelCommand::parse_from([
                "test",
                "--a-chain",
                "chain_a",
                "--a-connection",
                "connection_a",
                "--a-port",
                "port_id_a",
                "--b-port",
                "port_id_b"
            ])
        )
    }

    #[test]
    fn test_create_channel_version() {
        assert_eq!(
            CreateChannelCommand {
                chain_a: ChainId::from_string("chain_a"),
                chain_b: None,
                connection_a: Some(ConnectionId::from_str("connection_a").unwrap()),
                connection_hops: None,
                port_a: PortId::from_str("port_id_a").unwrap(),
                port_b: PortId::from_str("port_id_b").unwrap(),
                order: Ordering::Unordered,
                version: Some(Version::new("v1".to_owned())),
                new_client_connection: false,
                yes: false
            },
            CreateChannelCommand::parse_from([
                "test",
                "--a-chain",
                "chain_a",
                "--a-connection",
                "connection_a",
                "--a-port",
                "port_id_a",
                "--b-port",
                "port_id_b",
                "--channel-version",
                "v1"
            ])
        )
    }

    #[test]
    fn test_create_channel_order() {
        assert_eq!(
            CreateChannelCommand {
                chain_a: ChainId::from_string("chain_a"),
                chain_b: None,
                connection_a: Some(ConnectionId::from_str("connection_a").unwrap()),
                connection_hops: None,
                port_a: PortId::from_str("port_id_a").unwrap(),
                port_b: PortId::from_str("port_id_b").unwrap(),
                order: Ordering::Ordered,
                version: None,
                new_client_connection: false,
                yes: false
            },
            CreateChannelCommand::parse_from([
                "test",
                "--a-chain",
                "chain_a",
                "--a-connection",
                "connection_a",
                "--a-port",
                "port_id_a",
                "--b-port",
                "port_id_b",
                "--order",
                "ordered"
            ])
        )
    }

    #[test]
    fn test_create_channel_a_conn_alias() {
        assert_eq!(
            CreateChannelCommand {
                chain_a: ChainId::from_string("chain_a"),
                chain_b: None,
                connection_a: Some(ConnectionId::from_str("connection_a").unwrap()),
                connection_hops: None,
                port_a: PortId::from_str("port_id_a").unwrap(),
                port_b: PortId::from_str("port_id_b").unwrap(),
                order: Ordering::Unordered,
                version: None,
                new_client_connection: false,
                yes: false
            },
            CreateChannelCommand::parse_from([
                "test",
                "--a-chain",
                "chain_a",
                "--a-conn",
                "connection_a",
                "--a-port",
                "port_id_a",
                "--b-port",
                "port_id_b"
            ])
        )
    }

    #[test]
    fn test_create_channel_a_conn_with_new_client_conn() {
        assert!(CreateChannelCommand::try_parse_from([
            "test",
            "--a-chain",
            "chain_a",
            "--a-connection",
            "connection_a",
            "--a-port",
            "port_id_a",
            "--b-port",
            "port_id_b",
            "--new-client-connection"
        ])
        .is_err())
    }

    #[test]
    fn test_create_channel_a_conn_with_yes() {
        assert!(CreateChannelCommand::try_parse_from([
            "test",
            "--a-chain",
            "chain_a",
            "--b-chain",
            "chain_b",
            "--a-connection",
            "connection_a",
            "--a-port",
            "port_id_a",
            "--b-port",
            "port_id_b",
            "--order",
            "ordered",
            "--yes"
        ])
        .is_err())
    }

    #[test]
    fn test_create_channel_a_conn_with_b_chain() {
        assert!(CreateChannelCommand::try_parse_from([
            "test",
            "--a-chain",
            "chain_a",
            "--b-chain",
            "chain_b",
            "--a-connection",
            "connection_a",
            "--a-port",
            "port_id_a",
            "--b-port",
            "port_id_b",
            "--order",
            "ordered"
        ])
        .is_err())
    }

    #[test]
    fn test_create_channel_b_chain() {
        assert_eq!(
            CreateChannelCommand {
                chain_a: ChainId::from_string("chain_a"),
                chain_b: Some(ChainId::from_string("chain_b")),
                connection_a: None,
                connection_hops: None,
                port_a: PortId::from_str("port_id_a").unwrap(),
                port_b: PortId::from_str("port_id_b").unwrap(),
                order: Ordering::Unordered,
                version: None,
                new_client_connection: true,
                yes: false
            },
            CreateChannelCommand::parse_from([
                "test",
                "--a-chain",
                "chain_a",
                "--b-chain",
                "chain_b",
                "--a-port",
                "port_id_a",
                "--b-port",
                "port_id_b",
                "--new-client-connection"
            ])
        )
    }

    #[test]
    fn test_create_channel_b_chain_yes() {
        assert_eq!(
            CreateChannelCommand {
                chain_a: ChainId::from_string("chain_a"),
                chain_b: Some(ChainId::from_string("chain_b")),
                connection_a: None,
                connection_hops: None,
                port_a: PortId::from_str("port_id_a").unwrap(),
                port_b: PortId::from_str("port_id_b").unwrap(),
                order: Ordering::Unordered,
                version: None,
                new_client_connection: true,
                yes: true
            },
            CreateChannelCommand::parse_from([
                "test",
                "--a-chain",
                "chain_a",
                "--b-chain",
                "chain_b",
                "--a-port",
                "port_id_a",
                "--b-port",
                "port_id_b",
                "--new-client-connection",
                "--yes"
            ])
        )
    }

    #[test]
    fn test_create_channel_b_new_client_conn_alias() {
        assert_eq!(
            CreateChannelCommand {
                chain_a: ChainId::from_string("chain_a"),
                chain_b: Some(ChainId::from_string("chain_b")),
                connection_a: None,
                connection_hops: None,
                port_a: PortId::from_str("port_id_a").unwrap(),
                port_b: PortId::from_str("port_id_b").unwrap(),
                order: Ordering::Unordered,
                version: None,
                new_client_connection: true,
                yes: false
            },
            CreateChannelCommand::parse_from([
                "test",
                "--a-chain",
                "chain_a",
                "--b-chain",
                "chain_b",
                "--a-port",
                "port_id_a",
                "--b-port",
                "port_id_b",
                "--new-client-conn"
            ])
        )
    }

    #[test]
    fn test_create_channel_b_chain_without_new_client() {
        assert!(CreateChannelCommand::try_parse_from([
            "test",
            "--a-chain",
            "chain_a",
            "--b-chain",
            "chain_b",
            "--a-port",
            "port_id_a",
            "--b-port",
            "port_id_b"
        ])
        .is_err())
    }

    #[test]
    fn test_create_channel_no_b_port() {
        assert!(CreateChannelCommand::try_parse_from([
            "test",
            "--a-chain",
            "chain_a",
            "--b-chain",
            "chain_b",
            "--a-connection",
            "connection_a",
            "--a-port",
            "port_id_a"
        ])
        .is_err())
    }

    #[test]
    fn test_create_channel_no_a_port() {
        assert!(CreateChannelCommand::try_parse_from([
            "test",
            "--a-chain",
            "chain_a",
            "--b-chain",
            "chain_b",
            "--a-connection",
            "connection_a",
            "--b-port",
            "port_id_b"
        ])
        .is_err())
    }

    #[test]
    fn test_create_channel_no_b_chain_nor_a_conn() {
        assert!(CreateChannelCommand::try_parse_from([
            "test",
            "--a-chain",
            "chain_a",
            "--a-port",
            "port_id_a",
            "--b-port",
            "port_id_b"
        ])
        .is_err())
    }

    #[test]
    fn test_create_channel_no_a_chain() {
        assert!(CreateChannelCommand::try_parse_from([
            "test",
            "--b-chain",
            "chain_b",
            "--a-connection",
            "connection_a",
            "--a-port",
            "port_id_a",
            "--b-port",
            "port_id_b"
        ])
        .is_err())
    }
}
