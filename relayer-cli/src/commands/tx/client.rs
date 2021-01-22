use abscissa_core::{Command, Options, Runnable};

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::ClientId;
use relayer::chain::runtime::ChainRuntime;
use relayer::chain::CosmosSDKChain;
use relayer::config::ChainConfig;
use relayer::foreign_client::ForeignClient;

use crate::application::app_config;
use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: String,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: String,
}

/// Sample to run this tx:
///     `rrly -c loop_config.toml tx raw create-client ibc-0 ibc-1`
impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let (dst_chain_config, src_chain_config) =
            match validate_common_options(&self.dst_chain_id, &self.src_chain_id) {
                Ok(result) => result,
                Err(err) => {
                    return Output::error(err).exit();
                }
            };
        info!(
            "Message CreateClient for source chain: {:?}, on destination chain: {:?}",
            src_chain_config.id, dst_chain_config.id
        );

        let src_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config)
            .map_err(|e| Kind::Runtime.context(e));
        let src_chain = match src_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let dst_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config)
            .map_err(|e| Kind::Runtime.context(e));
        let dst_chain = match dst_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let client = ForeignClient {
            dst_chain,
            src_chain,
            id: ClientId::default(),
        };

        // Trigger client creation via the "build" interface, so that we obtain the resulting event
        let res: Result<IBCEvent, Error> = client
            .build_create_client_and_send()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpdateClientCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: String,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(
        free,
        required,
        help = "identifier of the client to be updated on destination chain"
    )]
    dst_client_id: ClientId,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        let opts = validate_common_options(&self.dst_chain_id, &self.src_chain_id);

        let (dst_chain_config, src_chain_config) = match opts {
            Ok(result) => result,
            Err(err) => {
                return Output::error(err).exit();
            }
        };

        info!(
            "Message UpdateClient client id: {:?}, for chain: {:?}, on chain: {:?}",
            self.dst_client_id.clone(),
            src_chain_config.id,
            dst_chain_config.id
        );

        let src_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config)
            .map_err(|e| Kind::Runtime.context(e));
        let src_chain = match src_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let dst_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config)
            .map_err(|e| Kind::Runtime.context(e));
        let dst_chain = match dst_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::error(format!("{}", e)).exit();
            }
        };

        let client = ForeignClient {
            dst_chain,
            src_chain,
            id: self.dst_client_id.clone(),
        };

        let res: Result<IBCEvent, Error> = client
            .build_update_client_and_send()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

fn validate_common_options(
    dst_chain_id: &str,
    src_chain_id: &str,
) -> Result<(ChainConfig, ChainConfig), String> {
    let config = app_config();

    // Validate parameters
    let dst_chain_id = dst_chain_id
        .parse()
        .map_err(|_| format!("bad destination chain ({}) identifier", dst_chain_id))?;

    let src_chain_id = src_chain_id
        .parse()
        .map_err(|_| format!("bad source chain ({}) identifier", src_chain_id))?;

    // Get the source and destination chain configuration
    let dst_chain_config = config
        .find_chain(&dst_chain_id)
        .ok_or_else(|| format!("missing destination chain ({}) configuration", dst_chain_id))?;

    let src_chain_config = config
        .find_chain(&src_chain_id)
        .ok_or_else(|| format!("missing source chain ({}) configuration", src_chain_id))?;

    Ok((dst_chain_config.clone(), src_chain_config.clone()))
}
