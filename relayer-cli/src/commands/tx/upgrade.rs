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

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxIbcUpgradeChainCmd {
    #[clap(
        long = "dst-chain",
        required = true,
        value_name = "DST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to upgrade"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "src-chain",
        required = true,
        value_name = "SRC_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the host chain"
    )]
    src_chain_id: ChainId,

    #[clap(
        long = "src-client",
        required = true,
        value_name = "SRC_CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client on the host chain from which the plan is created"
    )]
    src_client_id: ClientId,

    #[clap(
        long = "amount",
        required = true,
        value_name = "AMOUNT",
        help_heading = "REQUIRED",
        help = "Amount of stake"
    )]
    amount: u64,

    #[clap(
        long = "height-offset",
        required = true,
        value_name = "HEIGHT_OFFSET",
        help_heading = "REQUIRED",
        help = "Upgrade height offset in number of blocks since current"
    )]
    height_offset: u64,

    #[clap(
        long = "new-chain",
        value_name = "CHAIN_ID",
        help = "New chain identifier to assign to the upgrading chain (optional)"
    )]
    new_chain_id: Option<ChainId>,

    #[clap(
        long = "new-unbonding",
        value_name = "UNBONDING_PERIOD",
        help = "New unbonding period to assign to the upgrading chain, in seconds (optional)"
    )]
    new_unbonding: Option<u64>,

    #[clap(
        long = "upgrade-name",
        value_name = "UPGRADE_NAME",
        help = "A string to name the upgrade proposal plan (default: 'plan')"
    )]
    upgrade_name: Option<String>,

    #[clap(
        long = "denom",
        value_name = "DENOM",
        help = "Denomination for the deposit (default: 'stake')"
    )]
    denom: Option<String>,
}

impl TxIbcUpgradeChainCmd {
    fn validate_options(&self, config: &Config) -> Result<UpgradePlanOptions, String> {
        let host_chain_config = config.find_chain(&self.src_chain_id).ok_or_else(|| {
            format!(
                "missing configuration for source chain '{}'",
                self.src_chain_id
            )
        })?;

        let reference_chain_config = config.find_chain(&self.dst_chain_id).ok_or_else(|| {
            format!(
                "missing configuration for destination chain '{}'",
                self.dst_chain_id
            )
        })?;

        let opts = UpgradePlanOptions {
            dst_chain_config: reference_chain_config.clone(),
            src_chain_config: host_chain_config.clone(),
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

        let host_chain = spawn_chain_runtime(&config, &self.src_chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let reference_chain = spawn_chain_runtime(&config, &self.dst_chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = build_and_send_ibc_upgrade_proposal(reference_chain, host_chain, &opts)
            .map_err(Error::upgrade_chain);

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::TxIbcUpgradeChainCmd;

    use abscissa_core::clap::Parser;
    use ibc::core::ics24_host::identifier::{ChainId, ClientId};
    use std::str::FromStr;

    #[test]
    fn test_upgrade_chain_required_only() {
        assert_eq!(
            TxIbcUpgradeChainCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_client_id: ClientId::from_str("client_sender").unwrap(),
                amount: 42,
                height_offset: 21,
                new_chain_id: None,
                new_unbonding: None,
                upgrade_name: None,
                denom: None
            },
            TxIbcUpgradeChainCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-client",
                "client_sender",
                "--amount",
                "42",
                "--height-offset",
                "21"
            ])
        )
    }

    #[test]
    fn test_upgrade_chain_denom() {
        assert_eq!(
            TxIbcUpgradeChainCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_client_id: ClientId::from_str("client_sender").unwrap(),
                amount: 42,
                height_offset: 21,
                new_chain_id: None,
                new_unbonding: None,
                upgrade_name: None,
                denom: Some("my_denom".to_owned())
            },
            TxIbcUpgradeChainCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-client",
                "client_sender",
                "--amount",
                "42",
                "--height-offset",
                "21",
                "--denom",
                "my_denom"
            ])
        )
    }

    #[test]
    fn test_upgrade_chain_new_chain() {
        assert_eq!(
            TxIbcUpgradeChainCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_client_id: ClientId::from_str("client_sender").unwrap(),
                amount: 42,
                height_offset: 21,
                new_chain_id: Some(ChainId::from_string("new_chain")),
                new_unbonding: None,
                upgrade_name: None,
                denom: None
            },
            TxIbcUpgradeChainCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-client",
                "client_sender",
                "--amount",
                "42",
                "--height-offset",
                "21",
                "--new-chain",
                "new_chain"
            ])
        )
    }

    #[test]
    fn test_upgrade_chain_new_unbonding() {
        assert_eq!(
            TxIbcUpgradeChainCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_client_id: ClientId::from_str("client_sender").unwrap(),
                amount: 42,
                height_offset: 21,
                new_chain_id: None,
                new_unbonding: Some(17),
                upgrade_name: None,
                denom: None
            },
            TxIbcUpgradeChainCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-client",
                "client_sender",
                "--amount",
                "42",
                "--height-offset",
                "21",
                "--new-unbonding",
                "17"
            ])
        )
    }

    #[test]
    fn test_upgrade_chain_upgrade_name() {
        assert_eq!(
            TxIbcUpgradeChainCmd {
                dst_chain_id: ChainId::from_string("chain_receiver"),
                src_chain_id: ChainId::from_string("chain_sender"),
                src_client_id: ClientId::from_str("client_sender").unwrap(),
                amount: 42,
                height_offset: 21,
                new_chain_id: None,
                new_unbonding: None,
                upgrade_name: Some("upgrade_name".to_owned()),
                denom: None
            },
            TxIbcUpgradeChainCmd::parse_from(&[
                "test",
                "--dst-chain",
                "chain_receiver",
                "--src-chain",
                "chain_sender",
                "--src-client",
                "client_sender",
                "--amount",
                "42",
                "--height-offset",
                "21",
                "--upgrade-name",
                "upgrade_name"
            ])
        )
    }

    #[test]
    fn test_upgrade_chain_no_height_offset() {
        assert!(TxIbcUpgradeChainCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-chain",
            "chain_sender",
            "--src-client",
            "client_sender",
            "--amount",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_upgrade_chain_no_amount() {
        assert!(TxIbcUpgradeChainCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-chain",
            "chain_sender",
            "--src-client",
            "client_sender",
            "--height-offset",
            "21"
        ])
        .is_err())
    }

    #[test]
    fn test_upgrade_chain_no_sender_client() {
        assert!(TxIbcUpgradeChainCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-chain",
            "chain_sender",
            "--amount",
            "42",
            "--height-offset",
            "21"
        ])
        .is_err())
    }

    #[test]
    fn test_upgrade_chain_no_sender_chain() {
        assert!(TxIbcUpgradeChainCmd::try_parse_from(&[
            "test",
            "--dst-chain",
            "chain_receiver",
            "--src-client",
            "client_sender",
            "--amount",
            "42",
            "--height-offset",
            "21"
        ])
        .is_err())
    }

    #[test]
    fn test_upgrade_chain_no_receiver_chain() {
        assert!(TxIbcUpgradeChainCmd::try_parse_from(&[
            "test",
            "--src-chain",
            "chain_sender",
            "--src-client",
            "client_sender",
            "--amount",
            "42",
            "--height-offset",
            "21"
        ])
        .is_err())
    }
}
