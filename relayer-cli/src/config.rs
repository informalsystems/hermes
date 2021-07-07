//! Cli Config
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use std::collections::BTreeSet;

use thiserror::Error;

use ibc::ics24_host::identifier::ChainId;
use tendermint_light_client::types::TrustThreshold;

pub use ibc_relayer::config::Config;

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

/// Method for syntactic validation of the input configuration file.
pub fn validate_config(config: &Config) -> Result<(), Error> {
    // Check for duplicate chain configuration and invalid trust thresholds
    let mut unique_chain_ids = BTreeSet::new();
    for c in &config.chains {
        if !unique_chain_ids.insert(c.id.clone()) {
            return Err(Error::DuplicateChains(c.id.clone()));
        }

        validate_trust_threshold(&c.id, c.trust_threshold)?;
    }

    Ok(())
}

/// Check that the trust threshold is:
///
/// a) non-zero
/// b) greater or equal to 1/3
/// c) strictly less than 1
fn validate_trust_threshold(id: &ChainId, trust_threshold: TrustThreshold) -> Result<(), Error> {
    if trust_threshold.denominator == 0 {
        return Err(Error::InvalidTrustThreshold(
            trust_threshold,
            id.clone(),
            "trust threshold denominator cannot be zero".to_string(),
        ));
    }

    if trust_threshold.numerator * 3 < trust_threshold.denominator {
        return Err(Error::InvalidTrustThreshold(
            trust_threshold,
            id.clone(),
            "trust threshold cannot be < 1/3".to_string(),
        ));
    }

    if trust_threshold.numerator >= trust_threshold.denominator {
        return Err(Error::InvalidTrustThreshold(
            trust_threshold,
            id.clone(),
            "trust threshold cannot be >= 1".to_string(),
        ));
    }

    Ok(())
}
