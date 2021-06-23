use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::events::IbcEvent;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::upgrade_chain::{build_and_send_upgrade_chain_message, UpdatePlanOptions};
use ibc_relayer::{
    chain::{Chain, CosmosSdkChain},
    config::Config,
};

use crate::conclude::Output;
use crate::error::{self, Error};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpgradeChainCmd {
    #[options(free, required, help = "identifier of the chain to upgrade")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(
        free,
        required,
        help = "identifier of the client on source chain from which the plan is created"
    )]
    src_client_id: ClientId,

    #[options(free, required, help = "amount of stake")]
    amount: u64,

    #[options(
        free,
        required,
        help = "upgrade height offset in number of blocks since current"
    )]
    height_offset: u64,
}

impl TxUpgradeChainCmd {
    fn validate_options(&self, config: &Config) -> Result<UpdatePlanOptions, String> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id)
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let dst_chain_config = config
            .find_chain(&self.dst_chain_id)
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let opts = UpdatePlanOptions {
            dst_chain_config: dst_chain_config.clone(),
            src_chain_config: src_chain_config.clone(),
            src_client_id: self.src_client_id.clone(),
            amount: self.amount,
            height_offset: self.height_offset,
        };

        Ok(opts)
    }
}

impl Runnable for TxUpgradeChainCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());

        let src_chain_res = CosmosSdkChain::bootstrap(opts.src_chain_config.clone(), rt.clone())
            .map_err(error::relayer_error);
        let src_chain = match src_chain_res {
            Ok(chain) => chain,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let dst_chain_res = CosmosSdkChain::bootstrap(opts.dst_chain_config.clone(), rt)
            .map_err(error::relayer_error);
        let dst_chain = match dst_chain_res {
            Ok(chain) => chain,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let res: Result<Vec<IbcEvent>, Error> =
            build_and_send_upgrade_chain_message(dst_chain, src_chain, &opts)
                .map_err(error::upgrade_chain_error);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
