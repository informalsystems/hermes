use crate::prelude::*;

use crate::error::{Error, Kind};
use abscissa_core::{Command, Options, Runnable};
use relayer::config::Config;
use relayer::tx::connection::{conn_init, ConnectionOpenInitOptions};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawConnInitCmd {
    #[options(free, help = "identifier of the source chain")]
    src_chain_id: Option<String>,

    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: Option<String>,

    #[options(free, help = "identifier of the source client")]
    src_client_id: Option<String>,

    #[options(free, help = "identifier of the destination client")]
    dest_client_id: Option<String>,

    #[options(free, help = "identifier of the source connection")]
    src_connection_id: Option<String>,

    #[options(help = "identifier of the destination connection", short = "d")]
    dest_connection_id: Option<String>,
}

impl TxRawConnInitCmd {
    fn validate_options(&self, config: &Config) -> Result<ConnectionOpenInitOptions, String> {
        let src_chain_id = self
            .src_chain_id
            .clone()
            .ok_or_else(|| "missing source chain identifier".to_string())?;

        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let dest_chain_id = self
            .dest_chain_id
            .clone()
            .ok_or_else(|| "missing destination chain identifier".to_string())?;

        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let src_client_id = self
            .src_client_id
            .as_ref()
            .ok_or_else(|| "missing source client identifier".to_string())?
            .parse()
            .map_err(|_| "bad source client identifier".to_string())?;

        let src_connection_id = self
            .src_connection_id
            .as_ref()
            .ok_or_else(|| "missing source connection identifier".to_string())?
            .parse()
            .map_err(|_| "bad source connection identifier".to_string())?;

        let dest_client_id = self
            .dest_client_id
            .as_ref()
            .ok_or_else(|| "missing destination client identifier".to_string())?
            .parse()
            .map_err(|_| "bad destination client identifier".to_string())?;

        let dest_connection_id = self
            .dest_connection_id
            .as_ref()
            .map(|v| {
                v.parse()
                    .map_err(|_| "bad destination connection identifier".to_string())
            })
            .transpose()?;

        let opts = ConnectionOpenInitOptions {
            src_client_id,
            dest_client_id,
            src_connection_id,
            dest_connection_id,
            src_chain_config: src_chain_config.clone(),
            dest_chain_config: dest_chain_config.clone(),
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

        let res: Result<(), Error> = conn_init(opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("conn init, result: ", "{:?}", receipt),
            Err(e) => status_info!("conn init failed, error: ", "{}", e),
        }
    }
}
