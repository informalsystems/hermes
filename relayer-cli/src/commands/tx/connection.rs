use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::{ClientId, ConnectionId};

use relayer::config::ChainConfig;
use relayer::connection::{
    build_conn_ack_and_send, build_conn_confirm_and_send, build_conn_init_and_send,
    build_conn_try_and_send,
};

use crate::error::{Error, Kind};
use relayer::chain::runtime::ChainRuntime;
use relayer::connection::{ConnectionConfig, ConnectionSideConfig};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnInitCmd {
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

fn validate_common_options(
    dst_chain_id: &str,
    src_chain_id: &str,
) -> Result<(ChainConfig, ChainConfig), String> {
    let config = app_config();

    let dst_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == dst_chain_id.parse().unwrap())
        .ok_or_else(|| "missing destination chain configuration".to_string())?;

    let src_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == src_chain_id.parse().unwrap())
        .ok_or_else(|| "missing src chain configuration".to_string())?;

    Ok((dst_chain_config.clone(), src_chain_config.clone()))
}

impl Runnable for TxRawConnInitCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dst_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    status_err!("invalid options: {}", err);
                    return;
                }
            };

        let opts = ConnectionConfig {
            src_config: ConnectionSideConfig::new(
                src_chain_config.id.clone(),
                self.src_connection_id.clone(),
                self.src_client_id.clone(),
            ),
            dst_config: ConnectionSideConfig::new(
                dst_chain_config.id.clone(),
                self.dst_connection_id.clone(),
                self.dst_client_id.clone(),
            ),
        };

        status_info!("Message ConnOpenInit", "{:#?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_conn_init_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("conn init, result: ", "{:?}", receipt),
            Err(e) => status_info!("conn init failed, error: ", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnTryCmd {
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

impl Runnable for TxRawConnTryCmd {
    fn run(&self) {
        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dst_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    status_err!("invalid options: {}", err);
                    return;
                }
            };

        let opts = ConnectionConfig {
            src_config: ConnectionSideConfig::new(
                src_chain_config.id.clone(),
                self.src_connection_id.clone(),
                self.src_client_id.clone(),
            ),
            dst_config: ConnectionSideConfig::new(
                dst_chain_config.id.clone(),
                self.dst_connection_id.clone(),
                self.dst_client_id.clone(),
            ),
        };

        status_info!("Message ConnOpenTry", "{:#?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_conn_try_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("conn try, result: ", "{:?}", receipt),
            Err(e) => status_info!("conn try failed, error: ", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnAckCmd {
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

impl Runnable for TxRawConnAckCmd {
    fn run(&self) {
        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dst_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    status_err!("invalid options: {}", err);
                    return;
                }
            };

        let opts = ConnectionConfig {
            src_config: ConnectionSideConfig::new(
                src_chain_config.id.clone(),
                self.src_connection_id.clone(),
                self.src_client_id.clone(),
            ),
            dst_config: ConnectionSideConfig::new(
                dst_chain_config.id.clone(),
                self.dst_connection_id.clone(),
                self.dst_client_id.clone(),
            ),
        };

        status_info!("Message ConnOpenAck", "{:#?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config).unwrap();
        let res: Result<String, Error> = build_conn_ack_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("conn ack, result: ", "{:?}", receipt),
            Err(e) => status_info!("conn ack failed, error: ", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnConfirmCmd {
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

impl Runnable for TxRawConnConfirmCmd {
    fn run(&self) {
        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dst_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    status_err!("invalid options: {}", err);
                    return;
                }
            };

        let opts = ConnectionConfig {
            src_config: ConnectionSideConfig::new(
                src_chain_config.id.clone(),
                self.src_connection_id.clone(),
                self.src_client_id.clone(),
            ),
            dst_config: ConnectionSideConfig::new(
                dst_chain_config.id.clone(),
                self.dst_connection_id.clone(),
                self.dst_client_id.clone(),
            ),
        };

        status_info!("Message ConnOpenConfirm", "{:#?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_conn_confirm_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("conn confirm, result: ", "{:?}", receipt),
            Err(e) => status_info!("conn confirm failed, error: ", "{}", e),
        }
    }
}
