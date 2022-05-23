use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use alloc::sync::Arc;
use tokio::runtime::Runtime as TokioRuntime;

use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::chain::{ChainEndpoint, CosmosSdkChain};

use crate::application::app_config;
use crate::conclude::{exit_with_unrecoverable_error, Output};

#[derive(Clone, Command, Debug, Parser)]
pub struct KeyBalanceCmd {
    #[clap(required = true, help = "identifier of the chain")]
    chain_id: ChainId,

    #[clap(required = true, help = "name of the key")]
    keyname: String,
}

impl Runnable for KeyBalanceCmd {
    fn run(&self) {
        let config = app_config();

        let chain_config = match config.find_chain(&self.chain_id) {
            None => Output::error(format!(
                "chain {} not found in configuration file",
                self.chain_id
            ))
            .exit(),
            Some(chain_config) => chain_config,
        };

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSdkChain::bootstrap(chain_config.clone(), rt)
            .unwrap_or_else(exit_with_unrecoverable_error);

        match chain.query_balance() {
            Ok(balance) => {
                Output::success_msg(format!("balance {} {}", balance.amount, balance.denom)).exit()
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
