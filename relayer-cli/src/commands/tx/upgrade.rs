use core::time::Duration;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::config::Config;
use ibc_relayer::upgrade_chain::{build_and_send_ibc_upgrade_proposal, UpgradePlanOptions};

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct TxIbcUpgradeChainCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        help = "Identifier of the chain to upgrade"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        help = "Identifier of the source chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "src-client",
        required = true,
        help = "Identifier of the client on source chain from which the plan is created"
    )]
    src_client_id: ClientId,

    #[clap(long = "amount", required = true, help = "Amount of stake")]
    amount: u64,

    #[clap(
        long = "height-offset",
        required = true,
        help = "Upgrade height offset in number of blocks since current"
    )]
    height_offset: u64,

    #[clap(
        long = "new-chain",
        value_name = "CHAIN-ID",
        help = "New chain identifier to assign to the upgrading chain (optional)"
    )]
    new_chain_id: Option<ChainId>,

    #[clap(
        long = "new-unbonding",
        value_name = "PERIOD",
        help = "New unbonding period to assign to the upgrading chain, in seconds (optional)"
    )]
    new_unbonding: Option<u64>,

    #[clap(
        long = "upgrade-name",
        value_name = "NAME",
        help = "A string to name the upgrade proposal plan (default: 'plan')"
    )]
    upgrade_name: Option<String>,

    #[clap(
        long = "denom",
        help = "Denomination for the deposit (default: 'stake')"
    )]
    denom: Option<String>,
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

        let src_chain = spawn_chain_runtime(&config, &self.src_chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let dst_chain = spawn_chain_runtime(&config, &self.dst_chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = build_and_send_ibc_upgrade_proposal(dst_chain, src_chain, &opts)
            .map_err(Error::upgrade_chain);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
