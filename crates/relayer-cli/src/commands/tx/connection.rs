use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::connection::{Connection, ConnectionSide};
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::timestamp::ZERO_DURATION;

use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

macro_rules! conn_open_cmd {
    ($dbg_string:literal, $func:ident, $self:expr, $conn:expr) => {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &$self.src_chain_id, &$self.dst_chain_id)
        {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let connection = $conn(chains);

        debug!("message {}: {:?}", $dbg_string, connection);

        let res: Result<IbcEvent, Error> = connection.$func().map_err(Error::connection);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    };
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxConnInitCmd {
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
        long = "dst-client",
        required = true,
        value_name = "DST_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "src-client",
        required = true,
        value_name = "SRC_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source client"
    )]
    src_client_id: ClientId,
}

impl Runnable for TxConnInitCmd {
    fn run(&self) {
        conn_open_cmd!(
            "ConnOpenInit",
            build_conn_init_and_send,
            self,
            |chains: ChainHandlePair| {
                Connection {
                    delay_period: ZERO_DURATION,
                    a_side: ConnectionSide::new(chains.src, self.src_client_id.clone(), None),
                    b_side: ConnectionSide::new(chains.dst, self.dst_client_id.clone(), None),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxConnTryCmd {
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
        long = "dst-client",
        required = true,
        value_name = "DST_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "src-client",
        required = true,
        value_name = "SRC_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source client"
    )]
    src_client_id: ClientId,

    #[clap(
        long = "src-connection",
        visible_alias = "src-conn",
        required = true,
        value_name = "SRC_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source connection (required)"
    )]
    src_conn_id: ConnectionId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        value_name = "DST_CONNECTION_ID",
        help = "Identifier of the destination connection (optional)"
    )]
    dst_conn_id: Option<ConnectionId>,
}

impl Runnable for TxConnTryCmd {
    fn run(&self) {
        conn_open_cmd!(
            "ConnOpenTry",
            build_conn_try_and_send,
            self,
            |chains: ChainHandlePair| {
                Connection {
                    delay_period: ZERO_DURATION,
                    a_side: ConnectionSide::new(
                        chains.src,
                        self.src_client_id.clone(),
                        Some(self.src_conn_id.clone()),
                    ),
                    b_side: ConnectionSide::new(
                        chains.dst,
                        self.dst_client_id.clone(),
                        self.dst_conn_id.clone(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxConnAckCmd {
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
        long = "dst-client",
        required = true,
        value_name = "DST_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "src-client",
        required = true,
        value_name = "SRC_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source client"
    )]
    src_client_id: ClientId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        required = true,
        value_name = "DST_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination connection (required)"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "src-connection",
        visible_alias = "src-conn",
        required = true,
        value_name = "SRC_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source connection (required)"
    )]
    src_conn_id: ConnectionId,
}

impl Runnable for TxConnAckCmd {
    fn run(&self) {
        conn_open_cmd!(
            "ConnOpenAck",
            build_conn_ack_and_send,
            self,
            |chains: ChainHandlePair| {
                Connection {
                    delay_period: ZERO_DURATION,
                    a_side: ConnectionSide::new(
                        chains.src,
                        self.src_client_id.clone(),
                        Some(self.src_conn_id.clone()),
                    ),
                    b_side: ConnectionSide::new(
                        chains.dst,
                        self.dst_client_id.clone(),
                        Some(self.dst_conn_id.clone()),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxConnConfirmCmd {
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
        long = "dst-client",
        required = true,
        value_name = "DST_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "src-client",
        required = true,
        value_name = "SRC_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source client"
    )]
    src_client_id: ClientId,

    #[clap(
        long = "dst-connection",
        visible_alias = "dst-conn",
        required = true,
        value_name = "DST_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the destination connection (required)"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "src-connection",
        visible_alias = "src-conn",
        required = true,
        value_name = "SRC_CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the source connection (required)"
    )]
    src_conn_id: ConnectionId,
}

impl Runnable for TxConnConfirmCmd {
    fn run(&self) {
        conn_open_cmd!(
            "ConnOpenConfirm",
            build_conn_confirm_and_send,
            self,
            |chains: ChainHandlePair| {
                Connection {
                    delay_period: ZERO_DURATION,
                    a_side: ConnectionSide::new(
                        chains.src,
                        self.src_client_id.clone(),
                        Some(self.src_conn_id.clone()),
                    ),
                    b_side: ConnectionSide::new(
                        chains.dst,
                        self.dst_client_id.clone(),
                        Some(self.dst_conn_id.clone()),
                    ),
                }
            }
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{TxConnAckCmd, TxConnConfirmCmd, TxConnInitCmd, TxConnTryCmd};

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId, ConnectionId};

    #[test]
    fn test_conn_init() {
        assert_eq!(
            TxConnInitCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_client_id: ClientId::from_str("client_b-01").unwrap(),
                src_client_id: ClientId::from_str("client_a-01").unwrap()
            },
            TxConnInitCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-client",
                "client_b-01",
                "--src-client",
                "client_a-01"
            ])
        )
    }

    #[test]
    fn test_conn_init_no_a_client() {
        assert!(TxConnInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_init_no_b_client() {
        assert!(TxConnInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--src-client",
            "client_a-01"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_init_no_a_chain() {
        assert!(TxConnInitCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_init_no_b_chain() {
        assert!(TxConnInitCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_try_required_only() {
        assert_eq!(
            TxConnTryCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_client_id: ClientId::from_str("client_b-01").unwrap(),
                src_client_id: ClientId::from_str("client_a-01").unwrap(),
                src_conn_id: ConnectionId::from_str("connection_a").unwrap(),
                dst_conn_id: None
            },
            TxConnTryCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-client",
                "client_b-01",
                "--src-client",
                "client_a-01",
                "--src-connection",
                "connection_a"
            ])
        )
    }

    #[test]
    fn test_conn_try_b_connection() {
        assert_eq!(
            TxConnTryCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_client_id: ClientId::from_str("client_b-01").unwrap(),
                src_client_id: ClientId::from_str("client_a-01").unwrap(),
                src_conn_id: ConnectionId::from_str("connection_a").unwrap(),
                dst_conn_id: Some(ConnectionId::from_str("connection_b").unwrap())
            },
            TxConnTryCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-client",
                "client_b-01",
                "--src-client",
                "client_a-01",
                "--src-connection",
                "connection_a",
                "--dst-connection",
                "connection_b"
            ])
        )
    }

    #[test]
    fn test_conn_try_b_connection_aliases() {
        assert_eq!(
            TxConnTryCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_client_id: ClientId::from_str("client_b-01").unwrap(),
                src_client_id: ClientId::from_str("client_a-01").unwrap(),
                src_conn_id: ConnectionId::from_str("connection_a").unwrap(),
                dst_conn_id: Some(ConnectionId::from_str("connection_b").unwrap())
            },
            TxConnTryCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-client",
                "client_b-01",
                "--src-client",
                "client_a-01",
                "--src-conn",
                "connection_a",
                "--dst-conn",
                "connection_b"
            ])
        )
    }

    #[test]
    fn test_conn_try_no_a_connection() {
        assert!(TxConnTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_try_no_a_client() {
        assert!(TxConnTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_try_no_b_client() {
        assert!(TxConnTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--src-client",
            "client_a-01",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_try_no_a_chain() {
        assert!(TxConnTryCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_try_no_b_chain() {
        assert!(TxConnTryCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_ack() {
        assert_eq!(
            TxConnAckCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_client_id: ClientId::from_str("client_b-01").unwrap(),
                src_client_id: ClientId::from_str("client_a-01").unwrap(),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                src_conn_id: ConnectionId::from_str("connection_a").unwrap()
            },
            TxConnAckCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-client",
                "client_b-01",
                "--src-client",
                "client_a-01",
                "--dst-connection",
                "connection_b",
                "--src-connection",
                "connection_a"
            ])
        )
    }

    #[test]
    fn test_conn_ack_aliases() {
        assert_eq!(
            TxConnAckCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_client_id: ClientId::from_str("client_b-01").unwrap(),
                src_client_id: ClientId::from_str("client_a-01").unwrap(),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                src_conn_id: ConnectionId::from_str("connection_a").unwrap()
            },
            TxConnAckCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-client",
                "client_b-01",
                "--src-client",
                "client_a-01",
                "--dst-conn",
                "connection_b",
                "--src-conn",
                "connection_a"
            ])
        )
    }

    #[test]
    fn test_conn_ack_no_a_connection() {
        assert!(TxConnAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--dst-connection",
            "connection_b"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_ack_no_b_connection() {
        assert!(TxConnAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_ack_no_a_client() {
        assert!(TxConnAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--dst-connection",
            "connection_b",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_ack_no_b_client() {
        assert!(TxConnAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--src-client",
            "client_a-01",
            "--dst-connection",
            "connection_b",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_ack_no_a_chain() {
        assert!(TxConnAckCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--dst-connection",
            "connection_b",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_ack_no_b_chain() {
        assert!(TxConnAckCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--dst-connection",
            "connection_b",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_confirm() {
        assert_eq!(
            TxConnConfirmCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_client_id: ClientId::from_str("client_b-01").unwrap(),
                src_client_id: ClientId::from_str("client_a-01").unwrap(),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                src_conn_id: ConnectionId::from_str("connection_a").unwrap()
            },
            TxConnConfirmCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-client",
                "client_b-01",
                "--src-client",
                "client_a-01",
                "--dst-connection",
                "connection_b",
                "--src-connection",
                "connection_a"
            ])
        )
    }

    #[test]
    fn test_conn_confirm_aliases() {
        assert_eq!(
            TxConnConfirmCmd {
                dst_chain_id: ChainId::from_string("chain_b"),
                src_chain_id: ChainId::from_string("chain_a"),
                dst_client_id: ClientId::from_str("client_b-01").unwrap(),
                src_client_id: ClientId::from_str("client_a-01").unwrap(),
                dst_conn_id: ConnectionId::from_str("connection_b").unwrap(),
                src_conn_id: ConnectionId::from_str("connection_a").unwrap()
            },
            TxConnConfirmCmd::parse_from([
                "test",
                "--dst-chain",
                "chain_b",
                "--src-chain",
                "chain_a",
                "--dst-client",
                "client_b-01",
                "--src-client",
                "client_a-01",
                "--dst-conn",
                "connection_b",
                "--src-conn",
                "connection_a"
            ])
        )
    }

    #[test]
    fn test_conn_confirm_no_a_connection() {
        assert!(TxConnConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--dst-connection",
            "connection_b"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_confirm_no_b_connection() {
        assert!(TxConnConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_confirm_no_a_client() {
        assert!(TxConnConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--dst-connection",
            "connection_b",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_confirm_no_b_client() {
        assert!(TxConnConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--src-chain",
            "chain_a",
            "--src-client",
            "client_a-01",
            "--dst-connection",
            "connection_b",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_confirm_no_a_chain() {
        assert!(TxConnConfirmCmd::try_parse_from([
            "test",
            "--dst-chain",
            "chain_b",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--dst-connection",
            "connection_b",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }

    #[test]
    fn test_conn_confirm_no_b_chain() {
        assert!(TxConnConfirmCmd::try_parse_from([
            "test",
            "--src-chain",
            "chain_a",
            "--dst-client",
            "client_b-01",
            "--src-client",
            "client_a-01",
            "--dst-connection",
            "connection_b",
            "--src-connection",
            "connection_a"
        ])
        .is_err())
    }
}
