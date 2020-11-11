use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::{ClientId, ConnectionId};

use relayer::config::Config;
use relayer::tx::connection::{
    build_conn_init_and_send, build_conn_try_and_send, ConnectionOpenInitOptions,
    ConnectionOpenTryOptions,
};

use crate::error::{Error, Kind};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnInitCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination client")]
    dest_client_id: ClientId,

    #[options(free, help = "identifier of the source client")]
    src_client_id: ClientId,

    #[options(free, help = "identifier of the destination connection")]
    dest_connection_id: ConnectionId,

    #[options(help = "identifier of the source connection", short = "d")]
    src_connection_id: Option<ConnectionId>,

    #[options(
        help = "json key file for the signer, must include mnemonic",
        short = "k"
    )]
    seed_file: String,
}

impl TxRawConnInitCmd {
    fn validate_options(&self, config: &Config) -> Result<ConnectionOpenInitOptions, String> {
        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let signer_seed = std::fs::read_to_string(&self.seed_file).map_err(|e| {
            anomaly::Context::new("invalid signer seed file", Some(e.into())).to_string()
        })?;

        let opts = ConnectionOpenInitOptions {
            dest_chain_config: dest_chain_config.clone(),
            src_chain_config: src_chain_config.clone(),
            dest_client_id: self.dest_client_id.clone(),
            src_client_id: self.src_client_id.clone(),
            dest_connection_id: self.dest_connection_id.clone(),
            src_connection_id: self.src_connection_id.clone(),
            signer_seed,
        };

        Ok(opts)
    }
}

impl Runnable for TxRawConnInitCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", opts);

        let res: Result<String, Error> =
            build_conn_init_and_send(&opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("conn init, result: ", "{:?}", receipt),
            Err(e) => status_info!("conn init failed, error: ", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnTryCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination client")]
    dest_client_id: ClientId,

    #[options(free, help = "identifier of the source client")]
    src_client_id: ClientId,

    #[options(free, help = "identifier of the destination connection")]
    dest_connection_id: ConnectionId,

    #[options(free, help = "identifier of the source connection")]
    src_connection_id: ConnectionId,

    #[options(
        help = "json key file for the signer, must include mnemonic",
        short = "k"
    )]
    seed_file: String,
}

impl TxRawConnTryCmd {
    fn validate_options(&self, config: &Config) -> Result<ConnectionOpenTryOptions, String> {
        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let signer_seed = std::fs::read_to_string(&self.seed_file).map_err(|e| {
            anomaly::Context::new("invalid signer seed file", Some(e.into())).to_string()
        })?;

        let opts = ConnectionOpenTryOptions {
            src_chain_config: src_chain_config.clone(),
            dest_chain_config: dest_chain_config.clone(),
            src_client_id: self.src_client_id.clone(),
            dest_client_id: self.dest_client_id.clone(),
            src_connection_id: self.src_connection_id.clone(),
            dest_connection_id: self.dest_connection_id.clone(),
            signer_seed,
        };

        Ok(opts)
    }
}

impl Runnable for TxRawConnTryCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", opts);

        let res: Result<String, Error> =
            build_conn_try_and_send(opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("conn try, result: ", "{:?}", receipt),
            Err(e) => status_info!("conn try failed, error: ", "{}", e),
        }
    }
}
