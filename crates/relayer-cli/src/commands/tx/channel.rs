use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;
use humantime::Duration as HumanDuration;

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryConnectionRequest, QueryHeight};
use ibc_relayer::channel::{Channel, ChannelSide};

use ibc_relayer_types::core::ics03_connection::connection::ConnectionEnd;
use ibc_relayer_types::core::ics04_channel::channel::Ordering;
use ibc_relayer_types::core::ics04_channel::timeout::UpgradeTimeout;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::Height;

use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

/// Macro that generates the `Runnable::run` implementation for a
/// `tx channel` subcommand.
///
/// The macro takes the following arguments:
/// - `$dbg_string`: a string literal that will be used to identify the subcommand
///  in debug logs
/// - `$func`: the method that will be called to build and send the `Channel` message
/// - `$self`: the type that `Runnable` is being implemented for
/// - `$chan`: a closure that specifies how to build the `Channel` object
///
/// The macro spawns a `ChainHandlePair`, fetches the destination connection,
/// creates a `Channel` object via the closure, and then calls the `$func` method
/// with the `Channel` object.
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
}

impl Runnable for TxChanOpenInitCmd {
    fn run(&self) {
        tx_chan_cmd!(
            "ChanOpenInit",
            build_chan_open_init_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: self.order,
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        None,
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        None,
                        None,
                    ),
                }
            }
        );
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
        tx_chan_cmd!(
            "ChanOpenTry",
            build_chan_open_try_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Ordering::default(),
                    a_side: ChannelSide::new(
                        chains.src,
                        ClientId::default(),
                        ConnectionId::default(),
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        self.dst_chan_id.clone(),
                        None,
                    ),
                }
            }
        );
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
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
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
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
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
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
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
                        self.src_port_id.clone(),
                        Some(self.src_chan_id.clone()),
                        None,
                    ),
                    b_side: ChannelSide::new(
                        chains.dst,
                        dst_connection.client_id().clone(),
                        self.dst_conn_id.clone(),
                        self.dst_port_id.clone(),
                        Some(self.dst_chan_id.clone()),
                        None,
                    ),
                }
            }
        );
    }
}

/// Initiate a channel upgrade (ChannelUpgradeInit)
///
/// Build and send a `ChannelUpgradeInit` message to a destination
/// chain that the source chain has an already-existing channel open
/// with, signaling the intent by the source chain to perform
/// the channel upgrade handshake.
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanUpgradeInitCmd {
    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "dst-port",
        required = true,
        value_name = "DST_PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination port"
    )]
    dst_port_id: PortId,

    #[clap(
        long = "dst-channel",
        visible_alias = "dst-chan",
        required = true,
        value_name = "DST_CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination channel"
    )]
    dst_chan_id: ChannelId,

    #[clap(
        long = "version",
        required = false,
        value_name = "VERSION",
        help = "Version of the channel that both chains will upgrade to. Defaults to the version of the initiating chain if not specified."
    )]
    version: Option<Version>,

    #[clap(
        long = "ordering",
        required = false,
        value_name = "ORDERING",
        help = "Ordering of the channel that both chains will upgrade to. Note that the a channel may only be upgraded from a stricter ordering to a less strict ordering, i.e., from ORDERED to UNORDERED. Defaults to the ordering of the initiating chain if not specified."
    )]
    ordering: Option<Ordering>,

    #[clap(
        long = "connection-hops",
        required = false,
        value_name = "CONNECTION_HOPS",
        help = "Set of connection hops for the channel that both chains will upgrade to. Defaults to the connection hops of the initiating chain if not specified."
    )]
    connection_hops: Option<Vec<ConnectionId>>,

    #[clap(
        long = "timeout-height",
        required = false,
        value_name = "TIMEOUT_HEIGHT",
        help = "Height that, once it has been surpassed on the originating chain, the upgrade will time out. Required if no timeout timestamp is specified."
    )]
    timeout_height: Option<Height>,

    #[clap(
        long = "timeout-time",
        required = false,
        value_name = "TIMEOUT_TIME",
        help = "Timeout in human readable format since current that, once it has been surpassed on the originating chain, the upgrade will time out. Required if no timeout height is specified."
    )]
    timeout_time: Option<HumanDuration>,
}

impl Runnable for TxChanUpgradeInitCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let dst_chain_status = match chains.dst.query_application_status() {
            Ok(application_status) => application_status,
            Err(e) => Output::error(format!("query_application_status error {}", e)).exit(),
        };

        let timeout_timestamp = self
            .timeout_time
            .map(|timeout_time| (dst_chain_status.timestamp + *timeout_time).unwrap());

        // Check that at least one of timeout_height and timeout_timestamp has been provided
        let Ok(timeout) = UpgradeTimeout::new(self.timeout_height, timeout_timestamp) else {
            Output::error(
                "At least one of --timeout-height or --timeout-timestamp must be specified.",
            )
            .exit();
        };

        // Fetch the Channel that will facilitate the communication between the channel ends
        // being upgraded. This channel is assumed to already exist on the destination chain.
        let channel = Channel {
            connection_delay: Default::default(),
            ordering: Ordering::default(),
            a_side: ChannelSide::new(
                chains.src,
                ClientId::default(),
                ConnectionId::default(),
                PortId::default(),
                None,
                None,
            ),
            b_side: ChannelSide::new(
                chains.dst,
                ClientId::default(),
                ConnectionId::default(),
                self.dst_port_id.clone(),
                Some(self.dst_chan_id.clone()),
                None,
            ),
        };

        info!("message ChanUpgradeInit: {}", channel);

        let res: Result<IbcEvent, Error> = channel
            .build_chan_upgrade_init_and_send(
                self.version.clone(),
                self.ordering,
                self.connection_hops.clone(),
                timeout,
            )
            .map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

/// Relay the channel upgrade attempt (ChannelUpgradeTry)
///
/// Build and send a `ChannelUpgradeTry` message in response to
/// a `ChannelUpgradeInit` message, signaling the chain's intent to
/// cooperate with the source chain on upgrading the specified channel
/// and initiating the upgrade handshake.
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanUpgradeTryCmd {
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
        required = true,
        help_heading = "REQUIRED",
        value_name = "DST_CHANNEL_ID",
        help = "Identifier of the destination channel (optional)"
    )]
    dst_chan_id: Option<ChannelId>,

    #[clap(
        long = "timeout-height",
        required = false,
        value_name = "TIMEOUT_HEIGHT",
        help = "Height that, once it has been surpassed on the originating chain, the upgrade will time out. Required if no timeout timestamp is specified."
    )]
    timeout_height: Option<Height>,

    #[clap(
        long = "timeout-time",
        required = false,
        value_name = "TIMEOUT_TIME",
        help = "Timeout in human readable format since current that, once it has been surpassed on the originating chain, the upgrade will time out. Required if no timeout height is specified."
    )]
    timeout_time: Option<HumanDuration>,
}

impl Runnable for TxChanUpgradeTryCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let dst_chain_status = match chains.dst.query_application_status() {
            Ok(application_status) => application_status,
            Err(e) => Output::error(format!("query_application_status error {}", e)).exit(),
        };

        let timeout_timestamp = self
            .timeout_time
            .map(|timeout_time| (dst_chain_status.timestamp + *timeout_time).unwrap());

        // Check that at least one of timeout_height and timeout_timestamp has been provided
        let Ok(timeout) = UpgradeTimeout::new(self.timeout_height, timeout_timestamp) else {
            Output::error(
                "At least one of --timeout-height or --timeout-timestamp must be specified.",
            )
            .exit();
        };

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Retrieve the connection
        let dst_connection = match chains.dst.query_connection(
            QueryConnectionRequest {
                connection_id: self.dst_conn_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((connection, _)) => connection,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Fetch the Channel that will facilitate the communication between the channel ends
        // being upgraded. This channel is assumed to already exist on the destination chain.
        let channel = Channel {
            connection_delay: Default::default(),
            ordering: Ordering::default(),
            a_side: ChannelSide::new(
                chains.src,
                ClientId::default(),
                ConnectionId::default(),
                self.src_port_id.clone(),
                Some(self.src_chan_id.clone()),
                None,
            ),
            b_side: ChannelSide::new(
                chains.dst,
                dst_connection.client_id().clone(),
                self.dst_conn_id.clone(),
                self.dst_port_id.clone(),
                self.dst_chan_id.clone(),
                None,
            ),
        };

        info!("message ChanUpgradeTry: {}", channel);

        let res: Result<IbcEvent, Error> = channel
            .build_chan_upgrade_try_and_send(timeout)
            .map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

/// Relay the channel upgrade attempt (ChannelUpgradeAck)
///
/// Build and send a `ChannelUpgradeAck` message in response to
/// a `ChannelUpgradeTry` message in order to continue the channel
/// upgrade handshake.
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanUpgradeAckCmd {
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
        required = true,
        help_heading = "REQUIRED",
        value_name = "DST_CHANNEL_ID",
        help = "Identifier of the destination channel (optional)"
    )]
    dst_chan_id: Option<ChannelId>,
}

impl Runnable for TxChanUpgradeAckCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Retrieve the connection
        let dst_connection = match chains.dst.query_connection(
            QueryConnectionRequest {
                connection_id: self.dst_conn_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((connection, _)) => connection,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Fetch the Channel that will facilitate the communication between the channel ends
        // being upgraded. This channel is assumed to already exist on the destination chain.
        let channel = Channel {
            connection_delay: Default::default(),
            ordering: Ordering::default(),
            a_side: ChannelSide::new(
                chains.src,
                ClientId::default(),
                ConnectionId::default(),
                self.src_port_id.clone(),
                Some(self.src_chan_id.clone()),
                None,
            ),
            b_side: ChannelSide::new(
                chains.dst,
                dst_connection.client_id().clone(),
                self.dst_conn_id.clone(),
                self.dst_port_id.clone(),
                self.dst_chan_id.clone(),
                None,
            ),
        };

        info!("message ChanUpgradeAck: {}", channel);

        let res: Result<IbcEvent, Error> = channel
            .build_chan_upgrade_ack_and_send()
            .map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

/// Relay the channel upgrade attempt (ChannelUpgradeOpen)
///
/// Build and send a `ChannelUpgradeOpen` message to finalize
/// the channel upgrade handshake.
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxChanUpgradeOpenCmd {
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
        required = true,
        help_heading = "REQUIRED",
        value_name = "DST_CHANNEL_ID",
        help = "Identifier of the destination channel (optional)"
    )]
    dst_chan_id: Option<ChannelId>,
}

impl Runnable for TxChanUpgradeOpenCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Retrieve the connection
        let dst_connection = match chains.dst.query_connection(
            QueryConnectionRequest {
                connection_id: self.dst_conn_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((connection, _)) => connection,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Fetch the Channel that will facilitate the communication between the channel ends
        // being upgraded. This channel is assumed to already exist on the destination chain.
        let channel = Channel {
            connection_delay: Default::default(),
            ordering: Ordering::default(),
            a_side: ChannelSide::new(
                chains.src,
                ClientId::default(),
                ConnectionId::default(),
                self.src_port_id.clone(),
                Some(self.src_chan_id.clone()),
                None,
            ),
            b_side: ChannelSide::new(
                chains.dst,
                dst_connection.client_id().clone(),
                self.dst_conn_id.clone(),
                self.dst_port_id.clone(),
                self.dst_chan_id.clone(),
                None,
            ),
        };

        info!("message ChanUpgradeOpen: {}", channel);

        let res: Result<IbcEvent, Error> = channel
            .build_chan_upgrade_open_and_send()
            .map_err(Error::channel);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use abscissa_core::clap::Parser;
    use std::str::FromStr;

    use ibc_relayer_types::core::{
        ics04_channel::channel::Ordering,
        ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortId},
    };

    use crate::commands::tx::channel::{
        TxChanCloseConfirmCmd, TxChanCloseInitCmd, TxChanOpenAckCmd, TxChanOpenConfirmCmd,
        TxChanOpenInitCmd, TxChanOpenTryCmd,
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
                order: Ordering::Unordered
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
    fn test_chan_open_init_order() {
        assert_eq!(
            TxChanOpenInitCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                dst_port_id: PortId::from_str("port_b").unwrap(),
                src_port_id: PortId::from_str("port_a").unwrap(),
                order: Ordering::Ordered
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
                order: Ordering::Unordered
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
