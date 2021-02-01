use abscissa_core::{Command, Options, Runnable};

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc_relayer::config::StoreConfig;
use ibc_relayer::connection::{Connection, ConnectionSide};

use crate::commands::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

macro_rules! conn_open_cmd {
    ($dbg_string:literal, $func:ident, $self:expr, $conn:expr) => {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());
        let chains = match ChainHandlePair::spawn_with(
            spawn_options,
            &config,
            &$self.src_chain_id,
            &$self.dst_chain_id,
        ) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let connection = $conn(chains);

        info!("Message {}: {:?}", $dbg_string, connection);

        let res: Result<IBCEvent, Error> =
            connection.$func().map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    };
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnInitCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination client")]
    dst_client_id: ClientId,

    #[options(free, required, help = "identifier of the source client")]
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
                    a_side: ConnectionSide::new(
                        chains.src,
                        self.src_client_id.clone(),
                        ConnectionId::default(),
                    ),
                    b_side: ConnectionSide::new(
                        chains.dst,
                        self.dst_client_id.clone(),
                        ConnectionId::default(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnTryCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination client")]
    dst_client_id: ClientId,

    #[options(free, required, help = "identifier of the source client")]
    src_client_id: ClientId,

    #[options(required, help = "identifier of the source connection")]
    src_connection_id: ConnectionId,
}

impl Runnable for TxRawConnTryCmd {
    fn run(&self) {
        conn_open_cmd!(
            "ConnOpenTry",
            build_conn_try_and_send,
            self,
            |chains: ChainHandlePair| {
                Connection {
                    a_side: ConnectionSide::new(
                        chains.src,
                        self.src_client_id.clone(),
                        self.src_connection_id.clone(),
                    ),
                    b_side: ConnectionSide::new(
                        chains.dst,
                        self.dst_client_id.clone(),
                        ConnectionId::default(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnAckCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination client")]
    dst_client_id: ClientId,

    #[options(free, required, help = "identifier of the source client")]
    src_client_id: ClientId,

    #[options(required, help = "identifier of the destination connection")]
    dst_connection_id: ConnectionId,

    #[options(required, help = "identifier of the source connection")]
    src_connection_id: ConnectionId,
}

impl Runnable for TxRawConnAckCmd {
    fn run(&self) {
        conn_open_cmd!(
            "ConnOpenAck",
            build_conn_ack_and_send,
            self,
            |chains: ChainHandlePair| {
                Connection {
                    a_side: ConnectionSide::new(
                        chains.src,
                        self.src_client_id.clone(),
                        self.src_connection_id.clone(),
                    ),
                    b_side: ConnectionSide::new(
                        chains.dst,
                        self.dst_client_id.clone(),
                        self.dst_connection_id.clone(),
                    ),
                }
            }
        );
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnConfirmCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination client")]
    dst_client_id: ClientId,

    #[options(free, required, help = "identifier of the source client")]
    src_client_id: ClientId,

    #[options(required, help = "identifier of the destination connection")]
    dst_connection_id: ConnectionId,

    #[options(required, help = "identifier of the source connection")]
    src_connection_id: ConnectionId,
}

impl Runnable for TxRawConnConfirmCmd {
    fn run(&self) {
        conn_open_cmd!(
            "ConnOpenConfirm",
            build_conn_confirm_and_send,
            self,
            |chains: ChainHandlePair| {
                Connection {
                    a_side: ConnectionSide::new(
                        chains.src,
                        self.src_client_id.clone(),
                        self.src_connection_id.clone(),
                    ),
                    b_side: ConnectionSide::new(
                        chains.dst,
                        self.dst_client_id.clone(),
                        self.dst_connection_id.clone(),
                    ),
                }
            }
        );
    }
}
