use abscissa_core::{Command, Options, Runnable};
use relayer::config::Config;
use relayer::tx::client::{create_client, CreateClientOptions};

use crate::application::app_config;
use crate::error::{Error, Kind};
use crate::prelude::*;
use std::path::Path;
use std::fs;

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: Option<String>,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: Option<String>,

    #[options(free, help = "identifier of the client to be created on destination chain")]
    dest_client_id: Option<String>,

    #[options(free, help = "key file for the signer")]
    signer_key: Option<String>,
}

impl TxCreateClientCmd {
    fn validate_options(&self, config: &Config) -> Result<CreateClientOptions, String> {

        // Get content of key seed file
        let key_filename = self
            .signer_key
            .clone()
            .ok_or_else(|| "missing signer key file".to_string())?;

        let key_file = Path::new(&key_filename).exists();
        if !key_file {
            return Err("cannot find key file specified".to_string());
        }

        let key_file_contents = fs::read_to_string(key_filename)
            .expect("Something went wrong reading the key seed file");

        let dest_chain_id = self
            .dest_chain_id
            .clone()
            .ok_or_else(|| "missing destination chain identifier".to_string())?;

        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let src_chain_id = self
            .src_chain_id
            .clone()
            .ok_or_else(|| "missing source chain identifier".to_string())?;

        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing source chain configuration".to_string())?;

        let dest_client_id = self
            .dest_client_id
            .as_ref()
            .ok_or_else(|| "missing destination client identifier".to_string())?
            .parse()
            .map_err(|_| "bad client identifier".to_string())?;

        Ok(CreateClientOptions {
            dest_client_id,
            dest_chain_config: dest_chain_config.clone(),
            src_chain_config: src_chain_config.clone(),
            signer_key: key_file_contents
        })
    }
}

impl Runnable for TxCreateClientCmd {
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

        let res: Result<Vec<u8>, Error> = create_client(opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("client created, result: ", "{:?}", receipt),
            Err(e) => status_info!("client create failed, error: ", "{}", e),
        }
    }
}
