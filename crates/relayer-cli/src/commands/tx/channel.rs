#![allow(clippy::redundant_closure_call)]

use abscissa_core::clap::Parser;

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, QueryChannelRequest, QueryClientStateRequest, QueryConnectionRequest, QueryHeight,
};
use ibc_relayer::channel::{Channel, ChannelError, ChannelSide};
use ibc_relayer::connection::ConnectionError;
use ibc_relayer::registry::{set_global_registry, SharedRegistry};
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, IdentifiedConnectionEnd,
};
use ibc_relayer_types::core::ics04_channel::channel::Ordering;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, ConnectionIds, PortId,
};
use ibc_relayer_types::core::ics33_multihop::channel_path::{ConnectionHop, ConnectionHops};
use ibc_relayer_types::events::IbcEvent;

use crate::cli_utils::{spawn_chain_runtime, ChainHandlePair};
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

macro_rules! tx_chan_cmd {
    ($dbg_string:literal, $func:ident, $self:expr, $chan:expr) => {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &$self.src_chain_id, &$self.dst_chain_id)
        {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Retrieve the connection
        let dst_connection = match chains.dst.query_connection(
            QueryConnectionRequest {
                connection_id: $self.dst_conn_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((connection, _)) => connection,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        #[allow(clippy::redundant_closure_call)]
        let channel = $chan(chains, dst_connection);

        info!("message {}: {}", $dbg_string, channel);

        let res: Result<IbcEvent, Error> = channel.$func().map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    };
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanOpenInitCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        required = true,
        value_name = "DST_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination connection"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "dst-port",
        required = true,
        value_name = "DST_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination port"
    )]
    dst_port_id: PortId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "order",
        default_value_t,
        value_name = "ORDER",
        help = "The channel ordering, valid options 'unordered' (default) and 'ordered'"
    )]
    order: Ordering,

    #[clap(
        long = "connection-hops",
        value_name = "CONNECTION_HOPS",
        help = "A list of identifiers of the intermediate connections between \
        a destination and a source chain for a multi-hop channel, separated by slashes, \
        e.g, 'connection-1/connection-0' (optional)"
    )]
    conn_hop_ids: Option<ConnectionIds>,
}

impl Runnable for TxChanOpenInitCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(e).exit(),
        };

        // Attempt to retrieve --dst-connection
        let dst_connection = match chains.dst.query_connection(
            QueryConnectionRequest {
                connection_id: self.dst_conn_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((connection, _)) => connection,
            Err(e) => Output::error(e).exit(),
        };

        // There always exists at least one hop, even in single-hop channels.
        // A number of hops greater than one indicates a multi-hop channel.
        // See: https://github.com/cosmos/ibc/blob/main/spec/core/ics-033-multi-hop/README.md?plain=1#L62
        //
        // Start building the connection hops in reverse order, starting from --dst-connection and
        // moving towards the source.
        let dst_conn_client_state = match chains.dst.query_client_state(
            QueryClientStateRequest {
                client_id: dst_connection.client_id().clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((client_state, _)) => client_state,
            Err(e) => Output::error(e).exit(),
        };

        // Connection hops from b_side (--dst-chain) to a_side (--src-chain)
        let mut b_side_hops = Vec::new();

        // Build the first connection_hop, represented by --dst-connection
        b_side_hops.push(ConnectionHop {
            connection: IdentifiedConnectionEnd::new(
                self.dst_conn_id.clone(),
                dst_connection.clone(),
            ),
            src_chain_id: chains.dst.id(),
            dst_chain_id: dst_conn_client_state.chain_id().clone(),
        });

        // FIXME: We are not currently checking for cycles in channel paths, e.g, the following channel hops are valid:
        // ChainA -> ChainB -> ChainA -> ChainB. Still unsure if this should be allowed or not. Need to think about
        // possible ramifications.

        // Check if connection IDs were provided via --connection-hops, indicating a multi-hop channel
        if let Some(connnection_ids) = &self.conn_hop_ids {
            // Retrieve information for each of the remaining hops until the other end of the channel is reached
            for connection_id in connnection_ids.as_slice().iter() {
                // Retrieve the ChainId of the chain to which the last hop pointed to
                let chain_id = &b_side_hops.last().unwrap().dst_chain_id;

                // Spawn a handle for the chain pointed to by the previous hop
                let chain_handle = match spawn_chain_runtime(&config, chain_id) {
                    Ok(handle) => handle,
                    Err(e) => Output::error(e).exit(),
                };

                // Retrieve the connection associated with the next hop
                let hop_connection = match chain_handle.query_connection(
                    QueryConnectionRequest {
                        connection_id: connection_id.clone(),
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                ) {
                    Ok((connection, _)) => connection,
                    Err(e) => Output::error(e).exit(),
                };

                // Retrieve the state of the client underlying the hop connection
                let hop_conn_client_state = match chain_handle.query_client_state(
                    QueryClientStateRequest {
                        client_id: hop_connection.client_id().clone(),
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                ) {
                    Ok((client_state, _)) => client_state,
                    Err(e) => Output::error(e).exit(),
                };

                b_side_hops.push(ConnectionHop {
                    connection: IdentifiedConnectionEnd::new(connection_id.clone(), hop_connection),
                    src_chain_id: chain_id.clone(),
                    dst_chain_id: hop_conn_client_state.chain_id().clone(),
                });
            }
        }

        // Ensure that the channel path leads to the chain passed to --src-chain
        if let Some(last_hop) = &b_side_hops.last() {
            if last_hop.dst_chain_id != chains.src.id() {
                Output::error(Error::ics33_hops_destination_mismatch(
                    chains.src.id(),
                    chains.dst.id(),
                    last_hop.dst_chain_id.clone(),
                ))
                .exit()
            }
        }

        // FIXME: For now, pass Some(_) to connection_hops if there are multiple hops and None if there is a single one.
        // This allows us to keep using existing structs as they are defined (with the single `connection_id` field) while also including
        // the new `connection_hops` field. When multiple hops are present, pass Some(_) to connection_hops and use that.
        // When a single hop is present, pass None to connection_hops and use the connection_id stored in `ChannelSide`.
        let b_side_hops = match b_side_hops.len() {
            0 => Output::error("At least one connection hop is required for opening a channel.")
                .exit(),
            1 => None,
            _ => Some(ConnectionHops::new(b_side_hops)),
        };

        let channel = Channel {
            ordering: self.order,
            a_side: ChannelSide::new(
                chains.src,
                ClientId::default(),
                ConnectionId::default(),
                None,
                self.src_port_id.clone(),
                None,
                None,
            ),
            b_side: ChannelSide::new(
                chains.dst,
                dst_connection.client_id().clone(),
                self.dst_conn_id.clone(),
                b_side_hops,
                self.dst_port_id.clone(),
                None,
                None,
            ),
            connection_delay: Default::default(),
        };

        info!("message {}: {}", "ChanOpenInit", channel);

        let res: Result<IbcEvent, Error> = channel
            .build_chan_open_init_and_send()
            .map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanOpenTryCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        required = true,
        value_name = "DST_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination connection"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "dst-port",
        required = true,
        value_name = "DST_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination port"
    )]
    dst_port_id: PortId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "src-channel",
        visible_alias = "src-chan",
        required = true,
        value_name = "SRC_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source channel (required)"
    )]
    src_chan_id: ChannelId,

    #[clap(
        long = "dst-channel",
        visible_alias = "dst-chan",
        value_name = "DST_CHANNEL_ID",
        help = "Identifier of the destination channel (optional)"
    )]
    dst_chan_id: Option<ChannelId>,
}

impl Runnable for TxChanOpenTryCmd {
    fn run(&self) {
        let config = app_config();

        // Set a global registry to get_or_spawn() chain handles
        set_global_registry(SharedRegistry::new((*app_config()).clone()));

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(e).exit(),
        };

        // Attempt to retrieve --dst-connection
        let dst_connection = match chains.dst.query_connection(
            QueryConnectionRequest {
                connection_id: self.dst_conn_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((connection, _)) => connection,
            Err(e) => Output::error(e).exit(),
        };

        // Retrieve the ChannelEnd in INIT state (--src-channel) from --src-chain
        let init_channel = match chains.src.query_channel(
            QueryChannelRequest {
                port_id: self.src_port_id.clone(),
                channel_id: self.src_chan_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((channel, _)) => channel,
            Err(e) => Output::error(e).exit(),
        };

        let mut a_side_hops = Vec::new();
        let mut b_side_hops = Vec::new();

        // Determine if the channel is a multihop channel, i.e, connection_hops > 1
        if init_channel.connection_hops().len() > 1 {
            // In the case of multihop channels, we must build the channel path from --dst-chain
            // to --src-chain by leveraging the information stored in the existing ChannelEnd (which contains
            // the path from --src-chain to --dst-chain). We must traverse the path from --src-chain to
            // --dst-chain, and, for each connection hop, obtain the counterparty connection and use it
            // to build the same hop from the opposite direction.
            let mut chain_id = chains.src.id().clone();

            for a_side_connection_id in init_channel.connection_hops() {
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

                let counterparty_handle = match spawn_chain_runtime(&config, &counterparty_chain_id)
                {
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
        } else {
            // If the channel path corresponds to a single-hop channel, there is only one
            // connection hop from --dst-connection to --src-chain and vice-versa.

            // Get the single ConnectionId from a_side (--src-chain) to b_side (--dst-chain)
            // from the connection_hops field of the ChannelEnd in INIT state
            let a_side_connection_id =
                init_channel.connection_hops().first().unwrap_or_else(|| {
                    Output::error(ChannelError::missing_connection_hops(
                        self.src_chan_id.clone(),
                        self.src_chain_id.clone(),
                    ))
                    .exit()
                });

            let a_side_hop_connection = match chains.src.query_connection(
                QueryConnectionRequest {
                    connection_id: a_side_connection_id.clone().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            ) {
                Ok((connection, _)) => connection,
                Err(e) => Output::error(e).exit(),
            };

            let a_side_hop_conn_client_state = match chains.src.query_client_state(
                QueryClientStateRequest {
                    client_id: a_side_hop_connection.client_id().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            ) {
                Ok((client_state, _)) => client_state,
                Err(e) => Output::error(e).exit(),
            };

            a_side_hops.push(ConnectionHop {
                connection: IdentifiedConnectionEnd::new(
                    a_side_connection_id.clone(),
                    a_side_hop_connection,
                ),
                src_chain_id: chains.src.id(),
                dst_chain_id: a_side_hop_conn_client_state.chain_id(),
            });

            let b_side_hop_connection = match chains.dst.query_connection(
                QueryConnectionRequest {
                    connection_id: self.dst_conn_id.clone().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            ) {
                Ok((connection, _)) => connection,
                Err(e) => Output::error(e).exit(),
            };

            // Retrieve the state of the client underlying the hop connection
            let b_side_hop_conn_client_state = match chains.dst.query_client_state(
                QueryClientStateRequest {
                    client_id: b_side_hop_connection.client_id().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            ) {
                Ok((client_state, _)) => client_state,
                Err(e) => Output::error(e).exit(),
            };

            // Build the single hop from --dst-chain to --src-chain
            b_side_hops.push(ConnectionHop {
                connection: IdentifiedConnectionEnd::new(
                    self.dst_conn_id.clone(),
                    b_side_hop_connection.clone(),
                ),
                src_chain_id: chains.dst.id(),
                dst_chain_id: b_side_hop_conn_client_state.chain_id().clone(),
            });
        }

        // The connection hops were assembled while traversing from --src-chain towards --dst-chain.
        // Reverse them to obtain the path from --dst-chain to --src-chain. Single hops remain unchanged.
        b_side_hops.reverse();

        // Ensure that the reverse channel path correctly leads to the chain passed to --src-chain
        if let Some(last_hop) = &b_side_hops.last() {
            if last_hop.dst_chain_id != chains.src.id() {
                Output::error(Error::ics33_hops_destination_mismatch(
                    chains.src.id(),
                    chains.dst.id(),
                    last_hop.dst_chain_id.clone(),
                ))
                .exit()
            }
        }

        // FIXME: For now, pass Some(_) to connection_hops if there are multiple hops and None if there is a single one.
        // This allows us to keep using existing structs as they are defined (with the single `connection_id` field) while also including
        // the new `connection_hops` field. When multiple hops are present, pass Some(_) to connection_hops and use that.
        // When a single hop is present, pass None to connection_hops and use the connection_id stored in `ChannelSide`.
        let a_side_hops = match a_side_hops.len() {
            0 => Output::error("At least one connection hop is required for opening a channel.")
                .exit(),
            1 => None,
            _ => Some(ConnectionHops::new(a_side_hops)),
        };

        let b_side_hops = match b_side_hops.len() {
            0 => Output::error("At least one connection hop is required for opening a channel.")
                .exit(),
            1 => None,
            _ => Some(ConnectionHops::new(b_side_hops)),
        };

        let channel = Channel {
            ordering: Ordering::default(),
            a_side: ChannelSide::new(
                chains.src,
                ClientId::default(),
                ConnectionId::default(),
                a_side_hops,
                self.src_port_id.clone(),
                Some(self.src_chan_id.clone()),
                None,
            ),
            b_side: ChannelSide::new(
                chains.dst,
                dst_connection.client_id().clone(),
                self.dst_conn_id.clone(),
                b_side_hops,
                self.dst_port_id.clone(),
                self.dst_chan_id.clone(),
                None,
            ),
            connection_delay: Default::default(),
        };

        info!("message {}: {}", "ChanOpenTry", channel);

        let res: Result<IbcEvent, Error> = channel
            .build_chan_open_try_and_send()
            .map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanOpenAckCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        required = true,
        value_name = "DST_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination connection"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "dst-port",
        required = true,
        value_name = "DST_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination port"
    )]
    dst_port_id: PortId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "dst-channel",
        visible_alias = "dst-chan",
        required = true,
        value_name = "DST_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination channel (required)"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        long = "src-channel",
        visible_alias = "src-chan",
        required = true,
        value_name = "SRC_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source channel (required)"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxChanOpenAckCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanOpenAck",
            build_chan_open_ack_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Ordering::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        None,
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        None,
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id.clone()),
                        None,
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanOpenConfirmCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        required = true,
        value_name = "DST_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination connection"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "dst-port",
        required = true,
        value_name = "DST_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination port"
    )]
    dst_port_id: PortId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "dst-channel",
        visible_alias = "dst-chan",
        required = true,
        value_name = "DST_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination channel (required)"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        long = "src-channel",
        visible_alias = "src-chan",
        required = true,
        value_name = "SRC_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source channel (required)"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxChanOpenConfirmCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanOpenConfirm",
            build_chan_open_confirm_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Ordering::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        None,
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        None,
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id.clone()),
                        None,
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanCloseInitCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        required = true,
        value_name = "DST_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination connection"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "dst-port",
        required = true,
        value_name = "DST_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination port"
    )]
    dst_port_id: PortId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "dst-channel",
        visible_alias = "dst-chan",
        required = true,
        value_name = "DST_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination channel (required)"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        long = "src-channel",
        visible_alias = "src-chan",
        required = true,
        value_name = "SRC_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source channel (required)"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxChanCloseInitCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanCloseInit",
            build_chan_close_init_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Ordering::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        None,
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        None,
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id.clone()),
                        None,
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanCloseConfirmCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        required = true,
        value_name = "DST_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination connection"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "dst-port",
        required = true,
        value_name = "DST_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination port"
    )]
    dst_port_id: PortId,

    #[clap(
        long = "src-port",
        required = true,
        value_name = "SRC_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source port"
    )]
    src_port_id: PortId,

    #[clap(
        long = "dst-channel",
        visible_alias = "dst-chan",
        required = true,
        value_name = "DST_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination channel (required)"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        long = "src-channel",
        visible_alias = "src-chan",
        required = true,
        value_name = "SRC_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source channel (required)"
    )]
    src_chan_id: ChannelId,
}

impl Runnable for TxChanCloseConfirmCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanCloseConfirm",
            build_chan_close_confirm_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Ordering::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        None,
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        None,
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id.clone()),
                        None,
                    ),
                }
            }
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{
        TxChanCloseConfirmCmd, TxChanCloseInitCmd, TxChanOpenAckCmd, TxChanOpenConfirmCmd,
        TxChanOpenInitCmd, TxChanOpenTryCmd,
    };

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::{
        ics04_channel::channel::Ordering,
        ics24_host::identifier::{ChainId, ChannelId, ConnectionId, ConnectionIds, PortId},
    };

    #[test]
    fn test_chan_open_init_required_only() {
        assert_eq!(
            TxChanOpenInitCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                order: Ordering::Unordered,
                conn_hop_ids: None,
            },
            TxChanOpenInitCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a"
            ])
        )
    }

    #[test]
    fn test_chan_open_init_connection_hops() {
        assert_eq!(
            TxChanOpenInitCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                order: Ordering::Unordered,
                conn_hop_ids: Some(
                    ConnectionIds::from_str("connection_a/connection_b/connection_c").unwrap()
                )
            },
            TxChanOpenInitCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--connection-hops",
                "connection_a/connection_b/connection_c",
            ])
        )
    }

    #[test]
    fn test_chan_open_init_order() {
        assert_eq!(
            TxChanOpenInitCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                order: Ordering::Ordered,
                conn_hop_ids: None,
            },
            TxChanOpenInitCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--order",
                "ordered"
            ])
        )
    }

    #[test]
    fn test_chan_open_init_aliases() {
        assert_eq!(
            TxChanOpenInitCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                order: Ordering::Unordered,
                conn_hop_ids: None,
            },
            TxChanOpenInitCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-conn",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a"
            ])
        )
    }

    #[test]
    fn test_chan_open_init_no_a_port() {
        assert!(TxChanOpenInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_init_no_b_port() {
        assert!(TxChanOpenInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--src-port",
            "port_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_init_no_b_connection() {
        assert!(TxChanOpenInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_init_no_a_chain() {
        assert!(TxChanOpenInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_init_no_b_chain() {
        assert!(TxChanOpenInitCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_init_wrong_conn_hops_separator() {
        assert!(TxChanOpenInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--connection-hops",
            "connection-0,connection-1"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_try_required_only() {
        assert_eq!(
            TxChanOpenTryCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap(),
                dst_chan_id: None
            },
            TxChanOpenTryCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--src-channel",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_open_try_b_channel() {
        assert_eq!(
            TxChanOpenTryCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap(),
                dst_chan_id: Some(ChannelId::from_str("channel_b").unwrap())
            },
            TxChanOpenTryCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--src-channel",
                "channel_a",
                "--dst-channel",
                "channel_b"
            ])
        )
    }

    #[test]
    fn test_chan_open_try_aliases() {
        assert_eq!(
            TxChanOpenTryCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap(),
                dst_chan_id: Some(ChannelId::from_str("channel_b").unwrap())
            },
            TxChanOpenTryCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-conn",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--src-chan",
                "channel_a",
                "--dst-chan",
                "channel_b"
            ])
        )
    }

    #[test]
    fn test_chan_open_try_no_a_channel() {
        assert!(TxChanOpenTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_try_no_a_port() {
        assert!(TxChanOpenTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_try_no_b_port() {
        assert!(TxChanOpenTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--src-port",
            "port_a",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_try_no_b_connection() {
        assert!(TxChanOpenTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_try_no_a_chain() {
        assert!(TxChanOpenTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_try_no_b_chain() {
        assert!(TxChanOpenTryCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_ack() {
        assert_eq!(
            TxChanOpenAckCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                dst_chan_id: ChannelId::from_str("channel_b").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap()
            },
            TxChanOpenAckCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--dst-channel",
                "channel_b",
                "--src-channel",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_open_ack_aliases() {
        assert_eq!(
            TxChanOpenAckCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                dst_chan_id: ChannelId::from_str("channel_b").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap()
            },
            TxChanOpenAckCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-conn",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--dst-chan",
                "channel_b",
                "--src-chan",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_open_ack_no_a_channel() {
        assert!(TxChanOpenAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_ack_no_b_channel() {
        assert!(TxChanOpenAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_ack_no_a_port() {
        assert!(TxChanOpenAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_ack_no_b_port() {
        assert!(TxChanOpenAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_ack_no_b_connection() {
        assert!(TxChanOpenAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_ack_no_a_chain() {
        assert!(TxChanOpenAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_ack_no_b_chain() {
        assert!(TxChanOpenAckCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_confirm() {
        assert_eq!(
            TxChanOpenConfirmCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                dst_chan_id: ChannelId::from_str("channel_b").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap()
            },
            TxChanOpenConfirmCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--dst-channel",
                "channel_b",
                "--src-channel",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_open_confirm_aliases() {
        assert_eq!(
            TxChanOpenConfirmCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                dst_chan_id: ChannelId::from_str("channel_b").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap()
            },
            TxChanOpenConfirmCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-conn",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--dst-chan",
                "channel_b",
                "--src-chan",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_open_confirm_no_a_channel() {
        assert!(TxChanOpenConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_confirm_no_b_channel() {
        assert!(TxChanOpenConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_confirm_no_a_port() {
        assert!(TxChanOpenConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_confirm_no_b_port() {
        assert!(TxChanOpenConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_confirm_no_b_connection() {
        assert!(TxChanOpenConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_confirm_no_a_chain() {
        assert!(TxChanOpenConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_open_confirm_no_b_chain() {
        assert!(TxChanOpenConfirmCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_init() {
        assert_eq!(
            TxChanCloseInitCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                dst_chan_id: ChannelId::from_str("channel_b").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap()
            },
            TxChanCloseInitCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--dst-channel",
                "channel_b",
                "--src-channel",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_close_init_aliases() {
        assert_eq!(
            TxChanCloseInitCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                dst_chan_id: ChannelId::from_str("channel_b").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap()
            },
            TxChanCloseInitCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-conn",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--dst-chan",
                "channel_b",
                "--src-chan",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_close_init_no_a_channel() {
        assert!(TxChanCloseInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_init_no_b_channel() {
        assert!(TxChanCloseInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_init_no_a_port() {
        assert!(TxChanCloseInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_init_no_b_port() {
        assert!(TxChanCloseInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_init_no_b_connection() {
        assert!(TxChanCloseInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_init_no_a_chain() {
        assert!(TxChanCloseInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_init_no_b_chain() {
        assert!(TxChanCloseInitCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_confirm() {
        assert_eq!(
            TxChanCloseConfirmCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                dst_chan_id: ChannelId::from_str("channel_b").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap()
            },
            TxChanCloseConfirmCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-connection",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--dst-channel",
                "channel_b",
                "--src-channel",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_close_confirm_aliases() {
        assert_eq!(
            TxChanCloseConfirmCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                dst_chan_id: ChannelId::from_str("channel_b").unwrap(),
                src_chan_id: ChannelId::from_str("channel_a").unwrap()
            },
            TxChanCloseConfirmCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-conn",
                "connection_b",
                "--dst-port",
                "port_b",
                "--src-port",
                "port_a",
                "--dst-chan",
                "channel_b",
                "--src-chan",
                "channel_a"
            ])
        )
    }

    #[test]
    fn test_chan_close_confirm_no_a_channel() {
        assert!(TxChanCloseConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_confirm_no_b_channel() {
        assert!(TxChanCloseConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_confirm_no_a_port() {
        assert!(TxChanCloseConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_confirm_no_b_port() {
        assert!(TxChanCloseConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_confirm_no_b_connection() {
        assert!(TxChanCloseConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_confirm_no_a_chain() {
        assert!(TxChanCloseConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }

    #[test]
    fn test_chan_close_confirm_no_b_chain() {
        assert!(TxChanCloseConfirmCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-connection",
            "connection_b",
            "--dst-port",
            "port_b",
            "--src-port",
            "port_a",
            "--dst-channel",
            "channel_b",
            "--src-channel",
            "channel_a"
        ])
        .is_err())
    }
}
