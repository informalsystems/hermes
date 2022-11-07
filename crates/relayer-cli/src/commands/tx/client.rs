use core::{
    fmt::{Display, Error as FmtError, Formatter},
    time::Duration,
};
use std::thread;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, PageRequest, QueryClientStateRequest, QueryClientStatesRequest, QueryHeight,
};
use ibc_relayer::config::Config;
use ibc_relayer::event::IbcEventWithHeight;
use ibc_relayer::foreign_client::{CreateOptions, ForeignClient};
use ibc_relayer_types::core::ics02_client::client_state::ClientState;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::Height;
use tendermint_light_client_verifier::types::TrustThreshold;
use tracing::debug;

use crate::application::app_config;
use crate::cli_utils::{spawn_chain_runtime, spawn_chain_runtime_generic, ChainHandlePair};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxCreateClientCmd {
    #[clap(
        long = "host-chain",
        required = true,
        value_name = "HOST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain that hosts the client"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "reference-chain",
        required = true,
        value_name = "REFERENCE_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain targeted by the client"
    )]
    src_chain_id: ChainId,

    /// The maximum allowed clock drift for this client.
    ///
    /// The clock drift is a correction parameter. It helps deal with clocks
    /// that are only approximately synchronized between the source and destination chains
    /// of this client.
    /// The destination chain for this client uses the clock drift parameter when deciding
    /// to accept or reject a new header (originating from the source chain) for this client.
    /// If this option is not specified, a suitable clock drift value is derived from the chain
    /// configurations.
    #[clap(long = "clock-drift", value_name = "CLOCK_DRIFT")]
    clock_drift: Option<humantime::Duration>,

    /// Override the trusting period specified in the config.
    ///
    /// The trusting period specifies how long a validator set is trusted for
    /// (must be shorter than the chain's unbonding period).
    #[clap(long = "trusting-period", value_name = "TRUSTING_PERIOD")]
    trusting_period: Option<humantime::Duration>,

    /// Override the trust threshold specified in the configuration.
    ///
    /// The trust threshold defines what fraction of the total voting power of a known
    /// and trusted validator set is sufficient for a commit to be accepted going forward.
    #[clap(long = "trust-threshold", value_name = "TRUST_THRESHOLD", parse(try_from_str = parse_trust_threshold))]
    trust_threshold: Option<TrustThreshold>,
}

/// Sample to run this tx:
///     `hermes create client --host-chain ibc-0 --reference-chain ibc-1`
impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let config = app_config();

        if self.src_chain_id == self.dst_chain_id {
            Output::error("source and destination chains must be different".to_string()).exit()
        }

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient::restore(ClientId::default(), chains.dst, chains.src);

        let options = CreateOptions {
            max_clock_drift: self.clock_drift.map(Into::into),
            trusting_period: self.trusting_period.map(Into::into),
            trust_threshold: self.trust_threshold.map(Into::into),
        };

        // Trigger client creation via the "build" interface, so that we obtain the resulting event
        let res: Result<IbcEventWithHeight, Error> = client
            .build_create_client_and_send(options)
            .map_err(Error::foreign_client);

        match res {
            Ok(receipt) => Output::success(receipt.event).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxUpdateClientCmd {
    #[clap(
        long = "host-chain",
        required = true,
        value_name = "HOST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain that hosts the client"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "client",
        required = true,
        value_name = "CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain targeted by the client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "height",
        value_name = "REFERENCE_HEIGHT",
        help = "The target height of the client update. Leave unspecified for latest height."
    )]
    target_height: Option<u64>,

    #[clap(
        long = "trusted-height",
        value_name = "REFERENCE_TRUSTED_HEIGHT",
        help = "The trusted height of the client update. Leave unspecified for latest height."
    )]
    trusted_height: Option<u64>,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        let config = app_config();

        let dst_chain = match spawn_chain_runtime(&config, &self.dst_chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let src_chain_id = match dst_chain.query_client_state(
            QueryClientStateRequest {
                client_id: self.dst_client_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((cs, _)) => cs.chain_id(),
            Err(e) => {
                Output::error(format!(
                    "Query of client '{}' on chain '{}' failed with error: {}",
                    self.dst_client_id, self.dst_chain_id, e
                ))
                .exit();
            }
        };

        let src_chain = match spawn_chain_runtime(&config, &src_chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let target_height = self.target_height.map_or(QueryHeight::Latest, |height| {
            QueryHeight::Specific(
                Height::new(src_chain.id().version(), height)
                    .unwrap_or_else(exit_with_unrecoverable_error),
            )
        });

        let trusted_height = self.trusted_height.map(|height| {
            Height::new(src_chain.id().version(), height)
                .unwrap_or_else(exit_with_unrecoverable_error)
        });

        let client = ForeignClient::find(src_chain, dst_chain, &self.dst_client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = client
            .build_update_client_and_send(target_height, trusted_height)
            .map_err(Error::foreign_client);

        match res {
            Ok(events) => Output::success(events).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxUpgradeClientCmd {
    #[clap(
        long = "host-chain",
        required = true,
        value_name = "HOST_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain that hosts the client"
    )]
    chain_id: ChainId,

    #[clap(
        long = "client",
        required = true,
        value_name = "CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client to be upgraded"
    )]
    client_id: ClientId,

    #[clap(
        long = "upgrade-height",
        required = true,
        value_name = "REFERENCE_UPGRADE_HEIGHT",
        help_heading = "REQUIRED",
        help = "The height at which the reference chain halts for the client upgrade"
    )]
    reference_upgrade_height: u64,
}

impl Runnable for TxUpgradeClientCmd {
    fn run(&self) {
        let config = app_config();

        let host_chain = match spawn_chain_runtime(&config, &self.chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let reference_chain_id = match host_chain.query_client_state(
            QueryClientStateRequest {
                client_id: self.client_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((cs, _)) => cs.chain_id(),
            Err(e) => {
                Output::error(format!(
                    "Query of client '{}' on chain '{}' failed with error: {}",
                    self.client_id, self.chain_id, e
                ))
                .exit();
            }
        };

        let reference_chain = match spawn_chain_runtime(&config, &reference_chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient::find(reference_chain, host_chain, &self.client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // In order to perform the client upgrade, the chain is paused at the height specified by
        // the user. When the chain is paused, the application height reports a height of 1 less
        // than the height according to Tendermint. As a result, the target height at which the
        // upgrade occurs at (the application height) is 1 less than the height specified by
        // the user, hence the decrement of the upgrade height.
        let reference_upgrade_height = Height::new(
            client.src_chain().id().version(),
            self.reference_upgrade_height,
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        let target_reference_application_height = reference_upgrade_height
            .decrement()
            .expect("Upgrade height cannot be 1");

        let mut reference_application_latest_height = match client.src_chain().query_latest_height()
        {
            Ok(height) => height,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        debug!(
            "Reference application latest height: {}",
            reference_application_latest_height
        );

        while reference_application_latest_height != target_reference_application_height {
            thread::sleep(Duration::from_millis(500));

            reference_application_latest_height = match client.src_chain().query_latest_height() {
                Ok(height) => height,
                Err(e) => Output::error(format!("{}", e)).exit(),
            };

            debug!(
                "Reference application latest height: {}",
                reference_application_latest_height
            );
        }

        // sdk chains don't immediately update their stores after halting (at
        // least, as seen by the query interface). Sleep to avoid a race
        // condition with the chain
        thread::sleep(Duration::from_millis(6000));

        let outcome = client.upgrade(reference_upgrade_height);

        match outcome {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxUpgradeClientsCmd {
    #[clap(
        long = "reference-chain",
        required = true,
        value_name = "REFERENCE_CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain that underwent an upgrade; all clients targeting this chain will be upgraded"
    )]
    reference_chain_id: ChainId,

    #[clap(
        long = "upgrade-height",
        required = true,
        value_name = "REFERENCE_UPGRADE_HEIGHT",
        help_heading = "REQUIRED",
        help = "The height at which the reference chain halts for the client upgrade"
    )]
    reference_upgrade_height: u64,

    #[clap(
        long = "host-chain",
        value_name = "HOST_CHAIN_ID",
        help = "Identifier of the chain hosting the clients to be upgraded"
    )]
    host_chain_id: Option<ChainId>,
}

impl Runnable for TxUpgradeClientsCmd {
    fn run(&self) {
        let config = app_config();
        let reference_chain = match spawn_chain_runtime(&config, &self.reference_chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let reference_upgrade_height = Height::new(
            reference_chain.id().version(),
            self.reference_upgrade_height,
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        let target_reference_application_height = reference_upgrade_height
            .decrement()
            .expect("Upgrade height cannot be 1");

        let mut reference_application_latest_height = match reference_chain.query_latest_height() {
            Ok(height) => height,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        debug!(
            "Reference application latest height: {}",
            reference_application_latest_height
        );

        while reference_application_latest_height != target_reference_application_height {
            thread::sleep(Duration::from_millis(500));

            reference_application_latest_height = match reference_chain.query_latest_height() {
                Ok(height) => height,
                Err(e) => Output::error(format!("{}", e)).exit(),
            };

            debug!(
                "Reference application latest height: {}",
                reference_application_latest_height
            );
        }

        // sdk chains don't immediately update their stores after halting (at
        // least, as seen by the query interface). Sleep to avoid a race
        // condition with the chain
        thread::sleep(Duration::from_millis(6000));

        let results = config
            .chains
            .iter()
            .filter_map(|chain| {
                (self.reference_chain_id != chain.id
                    && (self.host_chain_id.is_none()
                        || self.host_chain_id == Some(chain.id.clone())))
                .then(|| {
                    self.upgrade_clients_for_chain(
                        &config,
                        reference_chain.clone(),
                        &chain.id,
                        reference_upgrade_height,
                    )
                })
            })
            .collect();

        let output = OutputBuffer(results);
        match output.into_result() {
            Ok(events) => Output::success(events).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

impl TxUpgradeClientsCmd {
    fn upgrade_clients_for_chain<Chain: ChainHandle>(
        &self,
        config: &Config,
        reference_chain: Chain,
        host_chain_id: &ChainId,
        reference_upgrade_height: Height,
    ) -> UpgradeClientsForChainResult {
        let host_chain = spawn_chain_runtime_generic::<Chain>(config, host_chain_id)?;

        let req = QueryClientStatesRequest {
            pagination: Some(PageRequest::all()),
        };
        let outputs = host_chain
            .query_clients(req)
            .map_err(Error::relayer)?
            .into_iter()
            .filter_map(|c| {
                (self.reference_chain_id == c.client_state.chain_id()).then_some(c.client_id)
            })
            .map(|id| {
                TxUpgradeClientsCmd::upgrade_client(
                    id,
                    host_chain.clone(),
                    reference_chain.clone(),
                    reference_upgrade_height,
                )
            })
            .collect();

        Ok(outputs)
    }

    fn upgrade_client<Chain: ChainHandle>(
        client_id: ClientId,
        host_chain: Chain,
        reference_chain: Chain,
        reference_upgrade_height: Height,
    ) -> Result<Vec<IbcEvent>, Error> {
        let client = ForeignClient::restore(client_id, host_chain, reference_chain);

        client
            .upgrade(reference_upgrade_height)
            .map_err(Error::foreign_client)
    }
}

fn parse_trust_threshold(input: &str) -> Result<TrustThreshold, Error> {
    let (num_part, denom_part) = input.split_once('/').ok_or_else(|| {
        Error::cli_arg("expected a fractional argument, two numbers separated by '/'".into())
    })?;
    let numerator = num_part
        .trim()
        .parse()
        .map_err(|_| Error::cli_arg("invalid numerator for the fraction".into()))?;
    let denominator = denom_part
        .trim()
        .parse()
        .map_err(|_| Error::cli_arg("invalid denominator for the fraction".into()))?;
    TrustThreshold::new(numerator, denominator)
        .map_err(|e| Error::cli_arg(format!("invalid trust threshold fraction: {}", e)))
}

type UpgradeClientResult = Result<Vec<IbcEvent>, Error>;
type UpgradeClientsForChainResult = Result<Vec<UpgradeClientResult>, Error>;

struct OutputBuffer(Vec<UpgradeClientsForChainResult>);

impl Display for OutputBuffer {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        fn sep<'a>(pos: usize, len: usize, other: &'a str, last: &'a str) -> &'a str {
            if pos != len - 1 {
                other
            } else {
                last
            }
        }

        let outer_results = &self.0;
        writeln!(f, ".")?;
        for (o, outer_result) in outer_results.iter().enumerate() {
            write!(f, "{}", sep(o, outer_results.len(), "├─", "└─"))?;
            match outer_result {
                Ok(inner_results) => {
                    writeln!(f, ".")?;
                    for (i, inner_result) in inner_results.iter().enumerate() {
                        write!(
                            f,
                            "{} {} ",
                            sep(o, outer_results.len(), "│", " "),
                            sep(i, inner_results.len(), "├─", "└─"),
                        )?;
                        match inner_result {
                            Ok(events) => writeln!(f, "{:#?}", events)?,
                            Err(e) => writeln!(f, "{}", e)?,
                        }
                    }
                }
                Err(e) => writeln!(f, " {}", e)?,
            }
        }
        Ok(())
    }
}

impl OutputBuffer {
    fn into_result(self) -> Result<Vec<Vec<IbcEvent>>, Self> {
        let mut all_events = vec![];
        let mut has_err = false;
        'outer: for outer_result in &self.0 {
            match outer_result {
                Ok(inner_results) => {
                    for inner_result in inner_results {
                        match inner_result {
                            Ok(events) => all_events.push(events.clone()),
                            Err(_) => {
                                has_err = true;
                                break 'outer;
                            }
                        }
                    }
                }
                Err(_) => {
                    has_err = true;
                    break 'outer;
                }
            }
        }
        if has_err {
            Err(self)
        } else {
            Ok(all_events)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        parse_trust_threshold, TxCreateClientCmd, TxUpdateClientCmd, TxUpgradeClientCmd,
        TxUpgradeClientsCmd,
    };

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use humantime::Duration;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
    use tendermint_light_client_verifier::types::TrustThreshold;

    #[test]
    fn test_parse_trust_threshold() {
        let threshold = parse_trust_threshold("3/5").unwrap();
        assert_eq!(threshold.numerator(), 3);
        assert_eq!(threshold.denominator(), 5);

        let threshold = parse_trust_threshold("3 / 5").unwrap();
        assert_eq!(threshold.numerator(), 3);
        assert_eq!(threshold.denominator(), 5);

        let threshold = parse_trust_threshold("\t3 / 5  ").unwrap();
        assert_eq!(threshold.numerator(), 3);
        assert_eq!(threshold.denominator(), 5);
    }

    #[test]
    fn test_create_client_required_only() {
        assert_eq!(
            TxCreateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                src_chain_id: ChainId::from_string("reference_chain"),
                clock_drift: None,
                trusting_period: None,
                trust_threshold: None
            },
            TxCreateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--reference-chain",
                "reference_chain"
            ])
        )
    }

    #[test]
    fn test_create_client_clock_drift() {
        assert_eq!(
            TxCreateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                src_chain_id: ChainId::from_string("reference_chain"),
                clock_drift: Some("5s".parse::<Duration>().unwrap()),
                trusting_period: None,
                trust_threshold: None
            },
            TxCreateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--reference-chain",
                "reference_chain",
                "--clock-drift",
                "5sec"
            ])
        );
        assert_eq!(
            TxCreateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                src_chain_id: ChainId::from_string("reference_chain"),
                clock_drift: Some("3s".parse::<Duration>().unwrap()),
                trusting_period: None,
                trust_threshold: None
            },
            TxCreateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--reference-chain",
                "reference_chain",
                "--clock-drift",
                "3s"
            ])
        );
    }

    #[test]
    fn test_create_client_trusting_period() {
        assert_eq!(
            TxCreateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                src_chain_id: ChainId::from_string("reference_chain"),
                clock_drift: None,
                trusting_period: Some("5s".parse::<Duration>().unwrap()),
                trust_threshold: None
            },
            TxCreateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--reference-chain",
                "reference_chain",
                "--trusting-period",
                "5sec"
            ])
        );
        assert_eq!(
            TxCreateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                src_chain_id: ChainId::from_string("reference_chain"),
                clock_drift: None,
                trusting_period: Some("3s".parse::<Duration>().unwrap()),
                trust_threshold: None
            },
            TxCreateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--reference-chain",
                "reference_chain",
                "--trusting-period",
                "3s"
            ])
        );
    }

    #[test]
    fn test_create_client_trust_threshold() {
        assert_eq!(
            TxCreateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                src_chain_id: ChainId::from_string("reference_chain"),
                clock_drift: None,
                trusting_period: None,
                trust_threshold: Some(TrustThreshold::new(1, 2).unwrap())
            },
            TxCreateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--reference-chain",
                "reference_chain",
                "--trust-threshold",
                "1/2"
            ])
        )
    }

    #[test]
    fn test_create_client_all_options() {
        assert_eq!(
            TxCreateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                src_chain_id: ChainId::from_string("reference_chain"),
                clock_drift: Some("5s".parse::<Duration>().unwrap()),
                trusting_period: Some("3s".parse::<Duration>().unwrap()),
                trust_threshold: Some(TrustThreshold::new(1, 2).unwrap())
            },
            TxCreateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--reference-chain",
                "reference_chain",
                "--clock-drift",
                "5sec",
                "--trusting-period",
                "3s",
                "--trust-threshold",
                "1/2"
            ])
        )
    }

    #[test]
    fn test_create_client_no_host_chain() {
        assert!(TxCreateClientCmd::try_parse_from([
            "test",
            "--reference-chain",
            "reference_chain",
            "--clock-drift",
            "5sec",
            "--trusting-period",
            "3s",
            "--trust-threshold",
            "1/2"
        ])
        .is_err())
    }

    #[test]
    fn test_create_client_no_reference_chain() {
        assert!(TxCreateClientCmd::try_parse_from([
            "test",
            "--host-chain",
            "host_chain",
            "--clock-drift",
            "5sec",
            "--trusting-period",
            "3s",
            "--trust-threshold",
            "1/2"
        ])
        .is_err())
    }

    #[test]
    fn test_create_client_no_chain() {
        assert!(TxCreateClientCmd::try_parse_from([
            "test",
            "--clock-drift",
            "5sec",
            "--trusting-period",
            "3s",
            "--trust-threshold",
            "1/2"
        ])
        .is_err())
    }

    #[test]
    fn test_update_client_required_only() {
        assert_eq!(
            TxUpdateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                dst_client_id: ClientId::from_str("client_to_update").unwrap(),
                target_height: None,
                trusted_height: None
            },
            TxUpdateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--client",
                "client_to_update"
            ])
        )
    }

    #[test]
    fn test_update_client_height() {
        assert_eq!(
            TxUpdateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                dst_client_id: ClientId::from_str("client_to_update").unwrap(),
                target_height: Some(42),
                trusted_height: None
            },
            TxUpdateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--client",
                "client_to_update",
                "--height",
                "42"
            ])
        )
    }

    #[test]
    fn test_update_client_trusted_height() {
        assert_eq!(
            TxUpdateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                dst_client_id: ClientId::from_str("client_to_update").unwrap(),
                target_height: None,
                trusted_height: Some(42)
            },
            TxUpdateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--client",
                "client_to_update",
                "--trusted-height",
                "42"
            ])
        )
    }

    #[test]
    fn test_update_client_all_options() {
        assert_eq!(
            TxUpdateClientCmd {
                dst_chain_id: ChainId::from_string("host_chain"),
                dst_client_id: ClientId::from_str("client_to_update").unwrap(),
                target_height: Some(21),
                trusted_height: Some(42)
            },
            TxUpdateClientCmd::parse_from([
                "test",
                "--host-chain",
                "host_chain",
                "--client",
                "client_to_update",
                "--height",
                "21",
                "--trusted-height",
                "42"
            ])
        )
    }

    #[test]
    fn test_update_client_no_chain() {
        assert!(TxUpdateClientCmd::try_parse_from([
            "test",
            "--client",
            "client_to_update",
            "--height",
            "21",
            "--trusted-height",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_update_client_no_client() {
        assert!(TxUpdateClientCmd::try_parse_from([
            "test",
            "--host-chain",
            "host_chain",
            "--height",
            "21",
            "--trusted-height",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_upgrade_client_required_only() {
        assert_eq!(
            TxUpgradeClientCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_to_upgrade").unwrap(),
                reference_upgrade_height: 42,
            },
            TxUpgradeClientCmd::parse_from([
                "test",
                "--host-chain",
                "chain_id",
                "--client",
                "client_to_upgrade",
                "--upgrade-height",
                "42"
            ])
        )
    }

    #[test]
    fn test_upgrade_client_no_chain() {
        assert!(TxUpgradeClientCmd::try_parse_from([
            "test",
            "--client",
            "client_to_upgrade",
            "--upgrade-height",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_upgrade_client_no_client() {
        assert!(TxUpgradeClientCmd::try_parse_from([
            "test",
            "--host-chain",
            "chain_id",
            "--upgrade-height",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_upgrade_client_no_upgrade_height() {
        assert!(TxUpgradeClientCmd::try_parse_from([
            "test",
            "--host-chain",
            "chain_id",
            "--client",
            "client_to_upgrade"
        ])
        .is_err())
    }

    #[test]
    fn test_upgrade_clients_required_only() {
        assert_eq!(
            TxUpgradeClientsCmd {
                reference_chain_id: ChainId::from_string("chain_id"),
                reference_upgrade_height: 42,
                host_chain_id: None,
            },
            TxUpgradeClientsCmd::parse_from([
                "test",
                "--reference-chain",
                "chain_id",
                "--upgrade-height",
                "42"
            ])
        )
    }

    #[test]
    fn test_upgrade_clients_host_chain() {
        assert_eq!(
            TxUpgradeClientsCmd {
                reference_chain_id: ChainId::from_string("chain_id"),
                reference_upgrade_height: 42,
                host_chain_id: Some(ChainId::from_string("chain_host_id")),
            },
            TxUpgradeClientsCmd::parse_from([
                "test",
                "--reference-chain",
                "chain_id",
                "--upgrade-height",
                "42",
                "--host-chain",
                "chain_host_id",
            ])
        )
    }

    #[test]
    fn test_upgrade_clients_no_upgrade_height() {
        assert!(
            TxUpgradeClientsCmd::try_parse_from(["test", "--reference-chain", "chain_id",])
                .is_err()
        )
    }

    #[test]
    fn test_upgrade_clients_no_chain() {
        assert!(TxUpgradeClientsCmd::try_parse_from(["test", "--upgrade-height", "42"]).is_err())
    }
}
