use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::ClientId;

use relayer::tx::client::{create_client, update_client, ClientOptions};

use crate::application::app_config;
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(
        free,
        help = "identifier of the client to be created on destination chain"
    )]
    dest_client_id: ClientId,

    #[options(help = "account sequence of the signer", short = "s")]
    account_sequence: u64,

    #[options(
        help = "json key file for the signer, must include mnemonic",
        short = "k"
    )]
    seed_file: String,
}

impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let opts = match validate_common_options(
            &self.dest_chain_id,
            &self.src_chain_id,
            &self.dest_client_id,
            self.account_sequence,
            &self.seed_file,
        ) {
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
            Ok(receipt) => status_ok!("Success", "client updated: {:?}", receipt),
            Err(e) => status_err!("client update failed: {}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpdateClientCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(
        free,
        help = "identifier of the client to be updated on destination chain"
    )]
    dest_client_id: ClientId,

    #[options(help = "account sequence of the signer", short = "s")]
    account_sequence: u64,

    #[options(
        help = "json key file for the signer, must include mnemonic",
        short = "k"
    )]
    seed_file: String,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        let opts = match validate_common_options(
            &self.dest_chain_id,
            &self.src_chain_id,
            &self.dest_client_id,
            self.account_sequence,
            &self.seed_file,
        ) {
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
            Ok(receipt) => status_ok!("Success", "client updated: {:?}", receipt),
            Err(e) => status_err!("client update failed: {}", e),
        }
    }
}

fn validate_common_options(
    dest_chain_id: &str,
    src_chain_id: &str,
    dest_client_id: &ClientId,
    account_sequence: u64,
    seed_file: &str,
) -> Result<ClientOptions, String> {
    let config = app_config();

    // Validate parameters
    let dest_chain_id = dest_chain_id
        .parse()
        .map_err(|_| "bad destination chain identifier".to_string())?;

    let src_chain_id = src_chain_id
        .parse()
        .map_err(|_| "bad source chain identifier".to_string())?;

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

    let signer_seed = std::fs::read_to_string(seed_file).map_err(|e| {
        anomaly::Context::new("invalid signer seed file", Some(e.into())).to_string()
    })?;

    Ok(ClientOptions {
        dest_client_id: dest_client_id.clone(),
        dest_chain_config: dest_chain_config.clone(),
        src_chain_config: src_chain_config.clone(),
        signer_seed,
        account_sequence,
    })
}
