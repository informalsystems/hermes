use abscissa_core::{Command, Options, Runnable};

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use relayer::connection::{Connection, ConnectionSide};

use crate::commands::cli_utils::chain_handlers_from_chain_id;
use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

macro_rules! conn_open_cmd {
    ($conn_open_cmd:ident, $dbg_string:literal, $func:ident) => {
        #[derive(Clone, Command, Debug, Options)]
        pub struct $conn_open_cmd {
            #[options(free, required, help = "identifier of the destination chain")]
            dst_chain_id: ChainId,

            #[options(free, required, help = "identifier of the source chain")]
            src_chain_id: ChainId,

            #[options(free, required, help = "identifier of the destination client")]
            dst_client_id: ClientId,

            #[options(free, required, help = "identifier of the source client")]
            src_client_id: ClientId,

            #[options(free, required, help = "identifier of the destination connection")]
            dst_connection_id: ConnectionId,

            #[options(free, required, help = "identifier of the source connection")]
            src_connection_id: ConnectionId,
        }

        impl Runnable for $conn_open_cmd {
            fn run(&self) {
                let config = app_config();

                let chains = match chain_handlers_from_chain_id(
                    config,
                    &self.src_chain_id,
                    &self.dst_chain_id,
                ) {
                    Ok(chains) => chains,
                    Err(e) => {
                        return Output::error(format!("{}", e)).exit();
                    }
                };

                let connection = Connection {
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
                };

                info!("Message {}: {:?}", $dbg_string, connection);

                let res: Result<IBCEvent, Error> =
                    connection.$func().map_err(|e| Kind::Tx.context(e).into());

                match res {
                    Ok(receipt) => Output::success(receipt).exit(),
                    Err(e) => Output::error(format!("{}", e)).exit(),
                }
            }
        }
    };
}

conn_open_cmd!(TxRawConnInitCmd, "ConnOpenInit", build_conn_init_and_send);

conn_open_cmd!(TxRawConnTryCmd, "ConnOpenTry", build_conn_try_and_send);

conn_open_cmd!(TxRawConnAckCmd, "ConnOpenAck", build_conn_ack_and_send);

conn_open_cmd!(
    TxRawConnConfirmCmd,
    "ConnOpenConfirm",
    build_conn_confirm_and_send
);
