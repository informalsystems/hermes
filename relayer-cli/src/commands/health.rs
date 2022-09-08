use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::chain::endpoint::HealthCheck::*;
use ibc_relayer::chain::handle::ChainHandle;

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct HealthCheckCmd {}

impl Runnable for HealthCheckCmd {
    fn run(&self) {
        let config = (*app_config()).clone();

        for ch in &config.chains {
            let _span = tracing::error_span!("health_check", chain = %ch.id).entered();

            info!("performing health check...");

            let chain =
                spawn_chain_runtime(&config, &ch.id).unwrap_or_else(exit_with_unrecoverable_error);

            match chain.health_check() {
                Ok(Healthy) => info!("chain is healthy"),
                Ok(Unhealthy(_)) => {
                    // No need to print the error here as it's already printed in `Chain::health_check`
                    // TODO(romac): Move the printing code here and in the supervisor/registry
                    warn!("chain is not healthy")
                }
                Err(e) => error!("failed to perform health check, reason: {}", e.detail()),
            }
        }

        Output::success_msg("performed health check for all chains in the config").exit()
    }
}
