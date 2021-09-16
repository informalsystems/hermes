use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc_relayer::chain::{ChainEndpoint, CosmosSdkChain, HealthCheck::*};

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct HealthCheckCmd {}

impl Runnable for HealthCheckCmd {
    fn run(&self) {
        let config = (*app_config()).clone();

        for ch in config.clone().chains {
            let rt = Arc::new(TokioRuntime::new().unwrap());

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

            info!("[{}] performing health check...", ch.id);

            let chain = CosmosSdkChain::bootstrap(chain_config.clone(), rt).unwrap();
            match chain.health_check() {
                Ok(Healthy) => info!("[{}] chain is healthy", ch.id),
                Ok(Unhealthy(e)) => error!("[{}] chain is unhealthy: {}", ch.id, e),
                Err(e) => error!("[{}] failed to perform health check: {}", ch.id, e),
            }
        }

        Output::success_msg("performed health check for all chains in the config").exit()
    }
}
