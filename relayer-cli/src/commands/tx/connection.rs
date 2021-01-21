use abscissa_core::{Command, Options, Runnable};
use serde_json::json;

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use relayer::chain::{runtime::ChainRuntime, CosmosSDKChain};
use relayer::connection::{
    build_conn_ack_and_send, build_conn_confirm_and_send, build_conn_init_and_send,
    build_conn_try_and_send,
};
use relayer::connection::{ConnectionConfig, ConnectionSideConfig};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

macro_rules! conn_open_cmd {
    ($conn_open_cmd:ident, $dbg_string:literal, $func:ident) => {
        #[derive(Clone, Command, Debug, Options)]
        pub struct $conn_open_cmd {
            #[options(free, help = "identifier of the destination chain")]
            dst_chain_id: String,

            #[options(free, help = "identifier of the source chain")]
            src_chain_id: String,

            #[options(free, help = "identifier of the destination client")]
            dst_client_id: ClientId,

            #[options(free, help = "identifier of the source client")]
            src_client_id: ClientId,

            #[options(free, help = "identifier of the destination connection")]
            dst_connection_id: ConnectionId,

            #[options(free, help = "identifier of the source connection")]
            src_connection_id: ConnectionId,
        }

        impl Runnable for $conn_open_cmd {
            fn run(&self) {
                let config = app_config();

                let src_config = config
                    .find_chain(&self.src_chain_id.parse().unwrap())
                    .ok_or_else(|| "missing src chain configuration".to_string());

                let dst_config = config
                    .find_chain(&self.dst_chain_id.parse().unwrap())
                    .ok_or_else(|| "missing src chain configuration".to_string());

                let (src_chain_config, dst_chain_config) = match (src_config, dst_config) {
                    (Ok(s), Ok(d)) => (s, d),
                    (_, _) => {
                        return Output::error(json!("invalid options")).exit();
                    }
                };

                let opts = ConnectionConfig {
                    a_config: ConnectionSideConfig::new(
                        src_chain_config.id.clone(),
                        self.src_client_id.clone(),
                        self.src_connection_id.clone(),
                    ),
                    b_config: ConnectionSideConfig::new(
                        dst_chain_config.id.clone(),
                        self.dst_client_id.clone(),
                        self.dst_connection_id.clone(),
                    ),
                };

                info!("Message {}: {:?}", $dbg_string, opts);

                let src_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config.clone())
                    .map_err(|e| Kind::Runtime.context(e));
                let src_chain = match src_chain_res {
                    Ok((handle, _)) => handle,
                    Err(e) => {
                        return Output::error(format!("{}", e)).exit();
                    }
                };

                let dst_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config.clone())
                    .map_err(|e| Kind::Runtime.context(e));
                let dst_chain = match dst_chain_res {
                    Ok((handle, _)) => handle,
                    Err(e) => {
                        return Output::error(format!("{}", e)).exit();
                    }
                };

                let res: Result<IBCEvent, Error> =
                    $func(dst_chain, src_chain, &opts).map_err(|e| Kind::Tx.context(e).into());

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
