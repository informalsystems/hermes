use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::events::IbcEvent;
use ibc::timestamp::ZERO_DURATION;
use ibc_relayer::connection::{Connection, ConnectionSide};

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

        debug!("Message {}: {:?}", $dbg_string, connection);

        let res: Result<IbcEvent, Error> = connection.$func().map_err(Error::connection);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    };
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawConnInitCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-client",
        required = true,
        help = "Identifier of the destination client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "src-client",
        required = true,
        help = "Identifier of the source client"
    )]
    src_client_id: ClientId,
}

impl Runnable for TxRawConnInitCmd {
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

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawConnTryCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-client",
        required = true,
        help = "Identifier of the destination client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "src-client",
        required = true,
        help = "Identifier of the source client"
    )]
    src_client_id: ClientId,

    #[clap(
        long = "src-connection",
        alias = "src-conn",
        required = true,
        help = "Identifier of the source connection (required)",
        value_name = "ID"
    )]
    src_conn_id: ConnectionId,

    #[clap(
        long = "dst-connection",
        alias = "dst-conn",
        help = "Identifier of the destination connection (optional)",
        value_name = "ID"
    )]
    dst_conn_id: Option<ConnectionId>,
}

impl Runnable for TxRawConnTryCmd {
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

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawConnAckCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-client",
        required = true,
        help = "Identifier of the destination client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "src-client",
        required = true,
        help = "Identifier of the source client"
    )]
    src_client_id: ClientId,

    #[clap(
        long = "dst-connection",
        alias = "dst-conn",
        required = true,
        help = "Identifier of the destination connection (required)",
        value_name = "ID"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "src-connection",
        alias = "src-conn",
        required = true,
        help = "Identifier of the source connection (required)",
        value_name = "ID"
    )]
    src_conn_id: ConnectionId,
}

impl Runnable for TxRawConnAckCmd {
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

#[derive(Clone, Command, Debug, Parser)]
pub struct TxRawConnConfirmCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        help = "Identifier of the destination chain"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "dst-client",
        required = true,
        help = "Identifier of the destination client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "src-client",
        required = true,
        help = "Identifier of the source client"
    )]
    src_client_id: ClientId,

    #[clap(
        long = "dst-connection",
        alias = "dst-conn",
        required = true,
        help = "Identifier of the destination connection (required)",
        value_name = "ID"
    )]
    dst_conn_id: ConnectionId,

    #[clap(
        long = "src-connection",
        alias = "src-conn",
        required = true,
        help = "Identifier of the source connection (required)",
        value_name = "ID"
    )]
    src_conn_id: ConnectionId,
}

impl Runnable for TxRawConnConfirmCmd {
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
