use core::fmt;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics24_host::identifier::{ChainId, ClientId};
use ibc::events::IbcEvent;
use ibc_proto::ibc::core::client::v1::QueryClientStatesRequest;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::{CreateOptions, ForeignClient};
use tendermint_light_client_verifier::types::TrustThreshold;

use crate::application::app_config;
use crate::cli_utils::{spawn_chain_runtime, spawn_chain_runtime_generic, ChainHandlePair};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;

#[derive(Clone, Command, Debug, Parser)]
pub struct TxCreateClientCmd {
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(required = true, help = "identifier of the source chain")]
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
    #[clap(short = 'd', long)]
    clock_drift: Option<humantime::Duration>,

    /// Override the trusting period specified in the config.
    ///
    /// The trusting period specifies how long a validator set is trusted for
    /// (must be shorter than the chain's unbonding period).
    #[clap(short = 'p', long)]
    trusting_period: Option<humantime::Duration>,

    /// Override the trust threshold specified in the configuration.
    ///
    /// The trust threshold defines what fraction of the total voting power of a known
    /// and trusted validator set is sufficient for a commit to be accepted going forward.
    #[clap(short = 't', long, parse(try_from_str = parse_trust_threshold))]
    trust_threshold: Option<TrustThreshold>,
}

/// Sample to run this tx:
///     `hermes tx raw create-client ibc-0 ibc-1`
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
    #[clap(required = true, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[clap(
        required = true,
        help = "identifier of the client to be updated on destination chain"
    )]
    dst_client_id: ClientId,

    #[clap(short = 'H', long, help = "the target height of the client update")]
    target_height: Option<u64>,

    #[clap(short = 't', long, help = "the trusted height of the client update")]
    trusted_height: Option<u64>,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        let config = app_config();

        let dst_chain = match spawn_chain_runtime(&config, &self.dst_chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let src_chain_id =
            match dst_chain.query_client_state(&self.dst_client_id, ibc::Height::zero()) {
                Ok(cs) => cs.chain_id(),
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

        let height = match self.target_height {
            Some(height) => ibc::Height::new(src_chain.id().version(), height),
            None => ibc::Height::zero(),
        };

        let trusted_height = match self.trusted_height {
            Some(height) => ibc::Height::new(src_chain.id().version(), height),
            None => ibc::Height::zero(),
        };

        let client = ForeignClient::find(src_chain, dst_chain, &self.dst_client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = client
            .build_update_client_and_send(height, trusted_height)
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
        required = true,
        help = "identifier of the chain that hosts the client"
    )]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the client to be upgraded")]
    client_id: ClientId,
}

impl Runnable for TxUpgradeClientCmd {
    fn run(&self) {
        let config = app_config();

        let dst_chain = match spawn_chain_runtime(&config, &self.chain_id) {
            Ok(handle) => handle,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        let src_chain_id = match dst_chain.query_client_state(&self.client_id, ibc::Height::zero())
        {
            Ok(cs) => cs.chain_id(),
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

        let outcome = client.upgrade();

        match outcome {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct TxUpgradeClientsCmd {
    #[clap(
        required = true,
        help = "identifier of the chain that underwent an upgrade; all clients targeting this chain will be upgraded"
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

        let results = config
            .chains
            .iter()
            .filter_map(|chain| {
                (self.src_chain_id != chain.id)
                    .then(|| self.upgrade_clients_for_chain(&config, src_chain.clone(), &chain.id))
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
    ) -> UpgradeClientsForChainResult {
        let dst_chain = spawn_chain_runtime_generic::<Chain>(config, dst_chain_id)?;

        let req = QueryClientStatesRequest {
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };
        let outputs = dst_chain
            .query_clients(req)
            .map_err(Error::relayer)?
            .into_iter()
            .filter_map(|c| (self.src_chain_id == c.client_state.chain_id()).then(|| c.client_id))
            .map(|id| TxUpgradeClientsCmd::upgrade_client(id, dst_chain.clone(), src_chain.clone()))
            .collect();

        Ok(outputs)
    }

    fn upgrade_client<Chain: ChainHandle>(
        client_id: ClientId,
        dst_chain: Chain,
        src_chain: Chain,
    ) -> Result<Vec<IbcEvent>, Error> {
        let client = ForeignClient::restore(client_id, dst_chain, src_chain);
        client.upgrade().map_err(Error::foreign_client)
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
