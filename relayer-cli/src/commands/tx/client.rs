use core::{fmt, time::Duration};
use std::thread;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics24_host::identifier::{ChainId, ClientId};
use ibc::events::IbcEvent;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, PageRequest, QueryClientStateRequest, QueryClientStatesRequest, QueryHeight,
};
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::{CreateOptions, ForeignClient};
use tendermint_light_client_verifier::types::TrustThreshold;
use tracing::info;

use crate::application::app_config;
use crate::cli_utils::{spawn_chain_runtime, spawn_chain_runtime_generic, ChainHandlePair};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;

#[derive(Clone, Command, Debug, Parser)]
pub struct TxCreateClientCmd {
    #[clap(
        long = "host-chain",
        required = true,
        value_name = "HOST_CHAIN_ID",
        help = "Identifier of the chain that hosts the client"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "reference-chain",
        required = true,
        value_name = "REFERENCE_CHAIN_ID",
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
///     `hermes tx raw create-client --dst-chain ibc-0 --src-chain ibc-1`
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
        let res: Result<IbcEvent, Error> = client
            .build_create_client_and_send(options)
            .map_err(Error::foreign_client);

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxUpdateClientCmd {
    #[clap(
        long = "host-chain",
        required = true,
        value_name = "HOST_CHAIN_ID",
        help = "Identifier of the chain that hosts the client"
    )]
    dst_chain_id: ChainId,

    #[clap(
        long = "client",
        required = true,
        value_name = "CLIENT_ID",
        help = "Identifier of the chain targeted by the client"
    )]
    dst_client_id: ClientId,

    #[clap(
        long = "height",
        value_name = "REFERENCE_HEIGHT",
        help = "The target height of the client update"
    )]
    target_height: Option<u64>,

    #[clap(
        long = "trusted-height",
        value_name = "REFERENCE_TRUSTED_HEIGHT",
        help = "The trusted height of the client update"
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
            QueryHeight::Specific(Height::new(src_chain.id().version(), height))
        });

        let trusted_height = self
            .trusted_height
            .map(|height| Height::new(src_chain.id().version(), height));

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

#[derive(Clone, Command, Debug, Parser)]
pub struct TxUpgradeClientCmd {
    #[clap(
        long = "host-chain",
        required = true,
        value_name = "HOST_CHAIN_ID",
        help = "Identifier of the chain that hosts the client"
    )]
    chain_id: ChainId,

    #[clap(
        long = "client",
        required = true,
        value_name = "CLIENT_ID",
        help = "Identifier of the client to be upgraded"
    )]
    client_id: ClientId,

    #[clap(
        long = "upgrade-height",
        required = true,
        value_name = "SRC_UPGRADE_HEIGHT",
        help = "The height at which the source chain should halt in order to perform the client upgrade"
    )]
    target_upgrade_height: Height,
}

impl Runnable for TxUpgradeClientCmd {
    fn run(&self) {
        let config = app_config();

        let dst_chain = match spawn_chain_runtime(&config, &self.chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let src_chain_id = match dst_chain.query_client_state(
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

        let src_chain = match spawn_chain_runtime(&config, &src_chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient::find(src_chain, dst_chain, &self.client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        // In order to perform the client upgrade, the chain is paused at the height specified by
        // the user. When the chain is paused, the application height reports a height of 1 less
        // than the height according to Tendermint. As a result, the target height at which the
        // upgrade occurs at (the application height) is 1 less than the height specified by
        // the user.
        let target_application_upgrade_height = match self.target_upgrade_height.decrement() {
            Ok(height) => height,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let mut src_application_latest_height = match client.src_chain().query_latest_height() {
            Ok(height) => height,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        info!(
            "Source application latest height: {}",
            src_application_latest_height
        );

        // Wait until the client's application height reaches the target application upgrade height
        while src_application_latest_height < target_application_upgrade_height {
            thread::sleep(Duration::from_millis(500));

            src_application_latest_height = match client.src_chain().query_latest_height() {
                Ok(height) => height,
                Err(e) => Output::error(format!("{}", e)).exit(),
            };

            info!(
                "Source application latest height: {}",
                src_application_latest_height
            );
        }

        let outcome = client.upgrade(self.target_upgrade_height);

        match outcome {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxUpgradeClientsCmd {
    #[clap(
        long = "reference-chain",
        required = true,
        value_name = "REFERENCE_CHAIN_ID",
        help = "Identifier of the chain that underwent an upgrade; all clients targeting this chain will be upgraded"
    )]
    src_chain_id: ChainId,
}

impl Runnable for TxUpgradeClientsCmd {
    fn run(&self) {
        let config = app_config();
        let src_chain = match spawn_chain_runtime(&config, &self.src_chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let src_upgrade_height = {
            let src_application_height = match src_chain.query_latest_height() {
                Ok(height) => height,
                Err(e) => Output::error(format!("{}", e)).exit(),
            };

            // When the chain is halted, the application height reports a height
            // 1 less than the halted height
            src_application_height.increment()
        };

        let results = config
            .chains
            .iter()
            .filter_map(|chain| {
                (self.src_chain_id != chain.id).then(|| {
                    self.upgrade_clients_for_chain(
                        &config,
                        src_chain.clone(),
                        &chain.id,
                        &src_upgrade_height,
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
        src_chain: Chain,
        dst_chain_id: &ChainId,
        src_upgrade_height: &Height,
    ) -> UpgradeClientsForChainResult {
        let dst_chain = spawn_chain_runtime_generic::<Chain>(config, dst_chain_id)?;

        let req = QueryClientStatesRequest {
            pagination: Some(PageRequest::all()),
        };
        let outputs = dst_chain
            .query_clients(req)
            .map_err(Error::relayer)?
            .into_iter()
            .filter_map(|c| (self.src_chain_id == c.client_state.chain_id()).then(|| c.client_id))
            .map(|id| {
                TxUpgradeClientsCmd::upgrade_client(
                    id,
                    dst_chain.clone(),
                    src_chain.clone(),
                    src_upgrade_height,
                )
            })
            .collect();

        Ok(outputs)
    }

    fn upgrade_client<Chain: ChainHandle>(
        client_id: ClientId,
        dst_chain: Chain,
        src_chain: Chain,
        src_upgrade_height: &Height,
    ) -> Result<Vec<IbcEvent>, Error> {
        let client = ForeignClient::restore(client_id, dst_chain, src_chain);

        client
            .upgrade(*src_upgrade_height)
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

impl fmt::Display for OutputBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
    use super::parse_trust_threshold;

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
}
