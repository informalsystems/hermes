use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::ClientId;

use relayer::tx::client::{
    build_create_client_and_send, build_update_client_and_send, ClientOptions,
};

use crate::application::app_config;
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, help = "identifier of the dstination chain")]
    dst_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(
        free,
        help = "identifier of the client to be created on dstination chain"
    )]
    dst_client_id: ClientId,

    #[options(
        help = "json key file for the signer, must include mnemonic",
        short = "k"
    )]
    seed_file: String,
}

impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let opts = match validate_common_options(
            &self.dst_chain_id,
            &self.src_chain_id,
            &self.dst_client_id,
            &self.seed_file,
        ) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", opts);

        let res: Result<String, Error> =
            build_create_client_and_send(opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_ok!("Success", "client created: {:?}", receipt),
            Err(e) => status_err!("client create failed: {}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpdateClientCmd {
    #[options(free, help = "identifier of the dstination chain")]
    dst_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(
        free,
        help = "identifier of the client to be updated on dstination chain"
    )]
    dst_client_id: ClientId,

    #[options(
        help = "json key file for the signer, must include mnemonic",
        short = "k"
    )]
    seed_file: String,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        let opts = validate_common_options(
            &self.dst_chain_id,
            &self.src_chain_id,
            &self.dst_client_id,
            &self.seed_file,
        );

        let opts = match opts {
            Ok(result) => result,
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
        };

        status_info!("Message", "{:?}", opts);

        let res: Result<String, Error> =
            build_update_client_and_send(opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_ok!("Success", "client updated: {:?}", receipt),
            Err(e) => status_err!("client update failed: {}", e),
        }
    }
}

fn validate_common_options(
    dst_chain_id: &str,
    src_chain_id: &str,
    dst_client_id: &ClientId,
    seed_file: &str,
) -> Result<ClientOptions, String> {
    let config = app_config();

    // Validate parameters
    let dst_chain_id = dst_chain_id
        .parse()
        .map_err(|_| "bad dstination chain identifier".to_string())?;

    let src_chain_id = src_chain_id
        .parse()
        .map_err(|_| "bad source chain identifier".to_string())?;

    // Get the source and dstination chain configuration
    let dst_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == dst_chain_id)
        .ok_or_else(|| "missing dstination chain configuration".to_string())?;

    let src_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == src_chain_id)
        .ok_or_else(|| "missing source chain configuration".to_string())?;

    let signer_seed = std::fs::read_to_string(seed_file).map_err(|e| {
        anomaly::Context::new("invalid signer seed file", Some(e.into())).to_string()
    })?;

    Ok(ClientOptions {
        dst_client_id: dst_client_id.clone(),
        dst_chain_config: dst_chain_config.clone(),
        src_chain_config: src_chain_config.clone(),
        signer_seed,
    })
}
