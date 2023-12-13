use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::event::IbcEventWithHeight;
use ibc_relayer::foreign_client::{CreateOptions, ForeignClient};

use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use tendermint_light_client_verifier::types::TrustThreshold;

use crate::application::app_config;
use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::error::Error;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct TxCreateVpClientCmd {
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
impl Runnable for TxCreateVpClientCmd {
    fn run(&self) {
        let config = app_config();

        if self.src_chain_id == self.dst_chain_id {
            Output::error("source and destination chains must be different".to_string()).exit()
        }

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => Output::error(e).exit(),
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
            Err(e) => Output::error(e).exit(),
        }
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
        .map_err(|e| Error::cli_arg(format!("invalid trust threshold fraction: {e}")))
}
