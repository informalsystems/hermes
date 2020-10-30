use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};
use relayer::tx::client::{create_client, update_client, CreateClientOptions, UpdateClientOptions};

use crate::application::app_config;
use crate::error::{Error, Kind};
use crate::prelude::*;
use ibc::ics24_host::identifier::ClientId;
use std::fs;
use std::path::Path;

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: Option<String>,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: Option<String>,

    #[options(
        free,
        help = "identifier of the client to be created on destination chain"
    )]
    dest_client_id: Option<String>,

    #[options(help = "account sequence of the signer", short = "s")]
    account_sequence: Option<String>,

    #[options(help = "key file for the signer", short = "k")]
    signer_key: Option<String>,
}

pub fn key_seed(
    account_sequence: Option<&String>,
    signer_key: Option<&String>,
) -> Result<(u64, String), String> {
    let parsed = account_sequence
        .clone()
        .ok_or_else(|| "missing account sequence".to_string())?
        .parse::<u64>();

    let acct_seq = match parsed {
        Ok(v) => v,
        Err(e) => return Err("invalid account sequence number".to_string()),
    };

    // Get content of key seed file
    let key_filename = signer_key
        .clone()
        .ok_or_else(|| "missing signer key file".to_string())?;

    let key_file = Path::new(&key_filename).exists();
    if !key_file {
        return Err("cannot find key file specified".to_string());
    }

    let key_seed =
        fs::read_to_string(key_filename).expect("Something went wrong reading the key seed file");

    Ok((acct_seq, key_seed))
}

impl TxCreateClientCmd {
    fn validate_options(&self, config: &Config) -> Result<CreateClientOptions, String> {
        let (dest_chain_config, src_chain_config, dest_client_id) = validate_common_options(
            &self.dest_chain_id,
            &self.src_chain_id,
            &self.dest_client_id,
            config,
        )?;

        let (account_sequence, signer_key) =
            key_seed(self.account_sequence.as_ref(), self.signer_key.as_ref())?;
        Ok(CreateClientOptions {
            dest_client_id,
            dest_chain_config,
            src_chain_config,
            signer_key,
            account_sequence,
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

        let res: Result<Vec<u8>, Error> =
            create_client(opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("client created, result: ", "{:?}", receipt),
            Err(e) => status_info!("client create failed, error: ", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpdateClientCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: Option<String>,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: Option<String>,

    #[options(
        free,
        help = "identifier of the client to be updated on destination chain"
    )]
    dest_client_id: Option<String>,

    #[options(help = "account sequence of the signer", short = "s")]
    account_sequence: Option<String>,

    #[options(help = "key file for the signer", short = "k")]
    signer_key: Option<String>,
}

impl TxUpdateClientCmd {
    fn validate_options(&self, config: &Config) -> Result<UpdateClientOptions, String> {
        let (dest_chain_config, src_chain_config, dest_client_id) = validate_common_options(
            &self.dest_chain_id,
            &self.src_chain_id,
            &self.dest_client_id,
            config,
        )?;

        let (account_sequence, signer_key) =
            key_seed(self.account_sequence.as_ref(), self.signer_key.as_ref())?;
        Ok(UpdateClientOptions {
            dest_client_id,
            dest_chain_config,
            src_chain_config,
            signer_key,
            account_sequence,
        })
    }
}

impl Runnable for TxUpdateClientCmd {
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

        let res: Result<Vec<u8>, Error> =
            update_client(opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("client updated, result: ", "{:?}", receipt),
            Err(e) => status_info!("client update failed, error: ", "{}", e),
        }
    }
}

fn validate_common_options(
    dest_chain_id: &Option<String>,
    src_chain_id: &Option<String>,
    dest_client_id: &Option<String>,
    config: &Config,
) -> Result<(ChainConfig, ChainConfig, ClientId), String> {
    // Validate parameters
    let dest_chain_id = dest_chain_id
        .clone()
        .ok_or_else(|| "missing destination chain identifier".to_string())?
        .parse()
        .map_err(|_| "bad destination chain identifier".to_string())?;

    let src_chain_id = src_chain_id
        .clone()
        .ok_or_else(|| "missing source chain identifier".to_string())?
        .parse()
        .map_err(|_| "bad source chain identifier".to_string())?;

    let dest_client_id = dest_client_id
        .as_ref()
        .ok_or_else(|| "missing destination client identifier".to_string())?
        .parse()
        .map_err(|_| "bad client identifier".to_string())?;

    // Get the source and destination chain configuration
    let dest_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == dest_chain_id)
        .ok_or_else(|| "missing destination chain configuration".to_string())?;

    let src_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == src_chain_id)
        .ok_or_else(|| "missing source chain configuration".to_string())?;

    Ok((
        dest_chain_config.clone(),
        src_chain_config.clone(),
        dest_client_id,
    ))
}
