//! Cli Config
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use std::collections::BTreeSet;

use thiserror::Error;

use ibc::ics24_host::identifier::ChainId;
pub use ibc_relayer::config::Config;
use tendermint_light_client::types::TrustThreshold;

/// Specifies all the possible syntactic errors
/// that a Hermes configuration file could contain.
#[derive(Error, Debug)]
pub enum Error {
    /// No chain is configured
    #[error("config file does not specify any chain")]
    ZeroChains,

    /// The log level is invalid
    #[error("config file specifies an invalid log level ('{0}'), caused by: {1}")]
    InvalidLogLevel(String, String),

    /// Duplicate chains configured
    #[error("config file has duplicate entry for the chain with id {0}")]
    DuplicateChains(ChainId),

    /// Invalid trust threshold
    #[error("config file specifies an invalid trust threshold ({0}) for the chain with id {1}, caused by: {2}")]
    InvalidTrustThreshold(TrustThreshold, ChainId, String),
}

/// Method for syntactic validation of the input
/// configuration file.
pub fn validate_config(config: &Config) -> Result<(), Error> {
    // Check for duplicate chain configuration and invalid trust-thresholds
    let mut unique_chain_ids = BTreeSet::new();
    for c in &config.chains {
        if !unique_chain_ids.insert(c.id.clone()) {
            return Err(Error::DuplicateChains(c.id.clone()));
        }

        // TODO: move below validation to tendermint::trust_threshold
        if c.trust_threshold.denominator == 0 {
            return Err(Error::InvalidTrustThreshold(
                c.trust_threshold,
                c.id.clone(),
                "Denominator cannot be zero".to_owned(),
            ));
        }
        if c.trust_threshold.numerator * 3 < c.trust_threshold.denominator {
            return Err(Error::InvalidTrustThreshold(
                c.trust_threshold,
                c.id.clone(),
                "Threshold cannot be < 1/3".to_owned(),
            ));
        }
        if c.trust_threshold.numerator >= c.trust_threshold.denominator {
            return Err(Error::InvalidTrustThreshold(
                c.trust_threshold,
                c.id.clone(),
                "Threshold cannot be >= 1".to_owned(),
            ));
        }
    }

    Ok(())
}
