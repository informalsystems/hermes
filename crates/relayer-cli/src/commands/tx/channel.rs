use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryConnectionRequest, QueryHeight};
use ibc_relayer::channel::{Channel, ChannelSide};
use ibc_relayer_types::core::ics03_connection::connection::ConnectionEnd;
use ibc_relayer_types::core::ics04_channel::channel::Order;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::events::IbcEvent;

use crate::cli_utils::ChainHandlePair;
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
    order: Order,
}

impl Runnable for TxChanOpenInitCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(e).exit(),
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
            Err(e) => Output::error(e).exit(),
        };

        let channel = Channel {
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
        };

        info!("message ChanOpenInit: {}", channel);

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
        tx_chan_cmd!(
            "ChanOpenTry",
            build_chan_open_try_and_send,
            self,
            |chains: ChainHandlePair, dst_connection: ConnectionEnd| {
                Channel {
                    connection_delay: Default::default(),
                    ordering: Order::default(),
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
                    ordering: Order::default(),
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
                    ordering: Order::default(),
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
                    ordering: Order::default(),
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
                    ordering: Order::default(),
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

#[cfg(test)]
mod tests {
    use super::{
        TxChanCloseConfirmCmd, TxChanCloseInitCmd, TxChanOpenAckCmd, TxChanOpenConfirmCmd,
        TxChanOpenInitCmd, TxChanOpenTryCmd,
    };

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::{
        ics04_channel::channel::Order,
        ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortId},
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
                order: Order::Unordered
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
                order: Order::Ordered
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
                order: Order::Unordered
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
