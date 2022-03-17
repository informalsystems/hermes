use alloc::sync::Arc;
use core::time::Duration;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::upgrade_chain::{build_and_send_ibc_upgrade_proposal, UpgradePlanOptions};
use ibc_relayer::{
    chain::{ChainEndpoint, CosmosSdkChain},
    config::Config,
};

use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct TxIbcUpgradeChainCmd {
    #[clap(required = true, help = "identifier of the chain to upgrade")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[clap(
        required = true,
        help = "identifier of the client on source chain from which the plan is created"
    )]
    src_client_id: ClientId,

    #[clap(required = true, help = "amount of stake")]
    amount: u64,

    #[clap(
        required = true,
        help = "upgrade height offset in number of blocks since current"
    )]
    height_offset: u64,

    #[clap(
        short = 'c',
        long,
        value_name = "CHAIN-ID",
        help = "new chain identifier to assign to the upgrading chain (optional)"
    )]
    new_chain_id: Option<ChainId>,

    #[clap(
        short = 'u',
        long,
        value_name = "PERIOD",
        help = "new unbonding period to assign to the upgrading chain, in seconds (optional)"
    )]
    new_unbonding: Option<u64>,

    #[clap(
        short = 'n',
        long,
        value_name = "NAME",
        help = "a string to name the upgrade proposal plan (default: 'plan')"
    )]
    upgrade_name: Option<String>,

    #[clap(
        short = 'd',
        long,
        help = "denomination for the deposit (default: 'stake')"
    )]
    denom: Option<String>,

    #[clap(
        short = 'l',
        long,
        help = "use legacy upgrade proposal constructs (for chains built with Cosmos SDK < v0.43.0)"
    )]
    legacy: bool,
}

impl TxIbcUpgradeChainCmd {
    fn validate_options(&self, config: &Config) -> Result<UpgradePlanOptions, String> {
        let src_chain_config = config.find_chain(&self.src_chain_id).ok_or_else(|| {
            format!(
                "missing configuration for source chain '{}'",
                self.src_chain_id
            )
        })?;

        let dst_chain_config = config.find_chain(&self.dst_chain_id).ok_or_else(|| {
            format!(
                "missing configuration for destination chain '{}'",
                self.dst_chain_id
            )
        })?;

        let opts = UpgradePlanOptions {
            dst_chain_config: dst_chain_config.clone(),
            src_chain_config: src_chain_config.clone(),
            src_client_id: self.src_client_id.clone(),
            amount: self.amount,
            denom: self.denom.as_deref().unwrap_or("stake").into(),
            height_offset: self.height_offset,
            upgraded_chain_id: self
                .new_chain_id
                .clone()
                .unwrap_or_else(|| self.dst_chain_id.clone()),
            upgraded_unbonding_period: self.new_unbonding.map(Duration::from_secs),
            upgrade_plan_name: self
                .upgrade_name
                .clone()
                .unwrap_or_else(|| "plan".to_string()),
            legacy: self.legacy,
        };

        Ok(opts)
    }
}

impl Runnable for TxIbcUpgradeChainCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => Output::error(err).exit(),
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());

        let src_chain_res = CosmosSdkChain::bootstrap(opts.src_chain_config.clone(), rt.clone())
            .map_err(Error::relayer);
        let src_chain = match src_chain_res {
            Ok(chain) => chain,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let dst_chain_res =
            CosmosSdkChain::bootstrap(opts.dst_chain_config.clone(), rt).map_err(Error::relayer);
        let dst_chain = match dst_chain_res {
            Ok(chain) => chain,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let res = build_and_send_ibc_upgrade_proposal(dst_chain, src_chain, &opts)
            .map_err(Error::upgrade_chain);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
