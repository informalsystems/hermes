use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::ClientId;

use crate::application::app_config;
use crate::error::{Error, Kind};
use crate::prelude::*;
use relayer::chain::runtime::ChainRuntime;
use relayer::chain::CosmosSDKChain;
use relayer::config::ChainConfig;
use relayer::foreign_client::{
    build_create_client_and_send, build_update_client_and_send, ForeignClientConfig,
};

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, help = "identifier of the destination chain")]
    dst_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(
        free,
        help = "identifier of the client to be created on destination chain"
    )]
    dst_client_id: ClientId,
}

impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let (dst_chain_config, src_chain_config, opts) = match validate_common_options(
            &self.dst_chain_id,
            &self.src_chain_id,
            &self.dst_client_id,
        ) {
            Ok(result) => result,
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
        };

        status_info!(
            "Message CreateClient",
            "id: {:?}, for chain: {:?}, on chain: {:?}",
            opts.client_id(),
            src_chain_config.id,
            opts.chain_id()
        );

        let (src_chain, _) = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_create_client_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_ok!("Success", "client created: {:?}", receipt),
            Err(e) => status_err!("client create failed: {}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpdateClientCmd {
    #[options(free, help = "identifier of the destination chain")]
    dst_chain_id: String,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(
        free,
        help = "identifier of the client to be updated on destination chain"
    )]
    dst_client_id: ClientId,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        let opts =
            validate_common_options(&self.dst_chain_id, &self.src_chain_id, &self.dst_client_id);

        let (dst_chain_config, src_chain_config, opts) = match opts {
            Ok(result) => result,
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
        };

        status_info!(
            "Message UpdateClient",
            "id: {:?}, for chain: {:?}, on chain: {:?}",
            opts.client_id(),
            src_chain_config.id,
            opts.chain_id()
        );

        let (src_chain, _) = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config).unwrap();
        let (dst_chain, _) = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config).unwrap();

        let res: Result<String, Error> = build_update_client_and_send(dst_chain, src_chain, &opts)
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_ok!("Success client updated: {:?}", receipt),
            Err(e) => status_err!("client update failed: {}", e),
        }
    }
}

fn validate_common_options(
    dst_chain_id: &str,
    src_chain_id: &str,
    dst_client_id: &ClientId,
) -> Result<(ChainConfig, ChainConfig, ForeignClientConfig), String> {
    let config = app_config();

    // Validate parameters
    let dst_chain_id = dst_chain_id
        .parse()
        .map_err(|_| "bad destination chain identifier".to_string())?;

    let src_chain_id = src_chain_id
        .parse()
        .map_err(|_| "bad source chain identifier".to_string())?;

    // Get the source and destination chain configuration
    let dst_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == dst_chain_id)
        .ok_or_else(|| "missing destination chain configuration".to_string())?;

    let src_chain_config = config
        .chains
        .iter()
        .find(|c| c.id == src_chain_id)
        .ok_or_else(|| "missing source chain configuration".to_string())?;

    Ok((
        dst_chain_config.clone(),
        src_chain_config.clone(),
        ForeignClientConfig::new(&dst_chain_config.id, &dst_client_id),
    ))
}
