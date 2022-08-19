//! Validation code for the Hermes configuration file.
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use alloc::collections::BTreeSet;
use std::path::PathBuf;

use flex_error::{define_error, TraceError};
use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::config::{ChainConfig, Config, ModeConfig};
use tendermint_light_client_verifier::types::TrustThreshold;
use tracing_subscriber::filter::ParseError;

use crate::application::app_reader;

/// Get the path to configuration file
pub fn config_path() -> Option<PathBuf> {
    let app = app_reader();
    app.config_path().cloned()
}

// Specifies all the possible syntactic errors
// that a Hermes configuration file could contain.
define_error! {
    Error {
        ZeroChain
            |_| { "config file does not specify any chain" },

        InvalidLogDirective
            { directive: String, }
            [ TraceError<ParseError> ]
            |e| {
                format!("invalid log directive: {0:?}", e.directive)
            },

        InvalidMode
            { reason: String, }
            |e| {
                format!("config file specifies invalid mode config, caused by: {0}",
                    e.reason)
            },

        DuplicateChains
            { chain_id: ChainId }
            |e| {
                format!("config file has duplicate entry for the chain '{0}'",
                    e.chain_id)
            },

        InvalidTrustThreshold
            {
                threshold: TrustThreshold,
                chain_id: ChainId,
                reason: String
            }
            |e| {
                format!("config file specifies an invalid `trust_threshold` ({0}) for the chain '{1}', caused by: {2}",
                    e.threshold, e.chain_id, e.reason)
            },

        DeprecatedGasAdjustment
            {
                gas_adjustment: f64,
                gas_multiplier: f64,
                chain_id: ChainId,
            }
            |e| {
                format!(
                    "config file specifies deprecated setting `gas_adjustment = {1}` for the chain '{0}'; \
                    to get the same behavior, use `gas_multiplier = {2}",
                    e.chain_id, e.gas_adjustment, e.gas_multiplier
                )
            },
    }
}

#[derive(Clone, Debug)]
pub enum Diagnostic<E> {
    Warning(E),
    Error(E),
}

/// Method for syntactic validation of the input configuration file.
pub fn validate_config(config: &Config) -> Result<(), Diagnostic<Error>> {
    // Check for duplicate chain configuration and invalid trust thresholds
    let mut unique_chain_ids = BTreeSet::new();
    for c in config.chains.iter() {
        let already_present = !unique_chain_ids.insert(c.id.clone());
        if already_present {
            return Err(Diagnostic::Error(Error::duplicate_chains(c.id.clone())));
        }

        validate_trust_threshold(&c.id, c.trust_threshold)?;

        // Validate gas-related settings
        validate_gas_settings(&c.id, c)?;
    }

    // Check for invalid mode config
    validate_mode(&config.mode)?;

    Ok(())
}

fn validate_mode(mode: &ModeConfig) -> Result<(), Diagnostic<Error>> {
    if mode.all_disabled() {
        return Err(Diagnostic::Warning(Error::invalid_mode(
            "all operation modes of Hermes are disabled, relayer won't perform any action aside from subscribing to events".to_string(),
        )));
    }

    if mode.clients.enabled && !mode.clients.refresh && !mode.clients.misbehaviour {
        return Err(Diagnostic::Error(Error::invalid_mode(
            "either `refresh` or `misbehaviour` must be set to true if `clients.enabled` is set to true".to_string(),
        )));
    }

    Ok(())
}

/// Check that the trust threshold is:
///
/// a) non-zero
/// b) greater or equal to 1/3
/// c) strictly less than 1
fn validate_trust_threshold(
    id: &ChainId,
    trust_threshold: TrustThreshold,
) -> Result<(), Diagnostic<Error>> {
    if trust_threshold.denominator() == 0 {
        return Err(Diagnostic::Error(Error::invalid_trust_threshold(
            trust_threshold,
            id.clone(),
            "trust threshold denominator cannot be zero".to_string(),
        )));
    }

    if trust_threshold.numerator() * 3 < trust_threshold.denominator() {
        return Err(Diagnostic::Error(Error::invalid_trust_threshold(
            trust_threshold,
            id.clone(),
            "trust threshold cannot be < 1/3".to_string(),
        )));
    }

    if trust_threshold.numerator() >= trust_threshold.denominator() {
        return Err(Diagnostic::Error(Error::invalid_trust_threshold(
            trust_threshold,
            id.clone(),
            "trust threshold cannot be >= 1".to_string(),
        )));
    }

    Ok(())
}

fn validate_gas_settings(id: &ChainId, config: &ChainConfig) -> Result<(), Diagnostic<Error>> {
    // Check that the gas_adjustment option is not set
    if let Some(gas_adjustment) = config.gas_adjustment {
        let gas_multiplier = gas_adjustment + 1.0;

        return Err(Diagnostic::Error(Error::deprecated_gas_adjustment(
            gas_adjustment,
            gas_multiplier,
            id.clone(),
        )));
    }

    Ok(())
}
