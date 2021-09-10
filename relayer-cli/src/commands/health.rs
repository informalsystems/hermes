use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};

use crate::conclude::Output;
use crate::prelude::*;
use ibc_relayer::chain::{ChainEndpoint, CosmosSdkChain};
use tokio::runtime::Runtime as TokioRuntime;

#[derive(Clone, Command, Debug, Options)]
pub struct HealthCheckCmd {}

impl Runnable for HealthCheckCmd {
    fn run(&self) {
        let config = (*app_config()).clone();

        for ch in config.clone().chains {
            let rt = Arc::new(TokioRuntime::new().unwrap());
            info!("Performing health check on chain {:?}...", ch.id);
            let chain_config = match config.find_chain(&ch.id) {
                None => {
                    return Output::error(format!(
                        "chain '{}' not found in configuration file",
                        ch.id
                    ))
                    .exit()
                }
                Some(chain_config) => chain_config,
            };
            let chain = CosmosSdkChain::bootstrap(chain_config.clone(), rt).unwrap();
            chain.health_checkup();
            chain.validate_params();
            info!("Performed health check on chain {:?}", ch.id);
        }
        info!("Hermes executed a health check for all chains in the config");
        Output::success_msg("done").exit()
    }
}
