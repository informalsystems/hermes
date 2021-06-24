use std::collections::BTreeSet;

use abscissa_core::config::Reader;
use abscissa_core::{Command, Options, Runnable};
use thiserror::Error;

use ibc::ics24_host::identifier::ChainId;

use crate::application::CliApp;
use crate::conclude::Output;
use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct ValidateCmd {}

/// Captures all the possible outcomes of performing syntactic
/// validation of a Hermes configuration file.
#[derive(Error, Debug)]
pub enum Diagnostic {
    /// Validation passed successfully
    #[error("config validation passed")]
    Ok,

    /// No chain was configured
    #[error("config file does not specify any chain")]
    ZeroChains,

    /// Only one chain was configured
    #[error("config file specifies a single chain, Hermes has limited functionality in this mode (e.g., some queries)")]
    OneChain,

    /// Duplicate chains configured
    #[error("config file has duplicate entry for the chain with id {0}")]
    DuplicateChains(ChainId),
}

/// Validation method for syntactic validation of the input
/// configuration file.
fn validate_config(config: Reader<CliApp>) -> Diagnostic {
    // Check for empty or solitary chains config.
    if config.chains.is_empty() {
        // No chain is preconfigured
        return Diagnostic::ZeroChains;
    } else if config.chains.len() == 1 {
        // Only one chain is preconfigured, not exactly an error but still useful to mention
        return Diagnostic::OneChain;
    }

    // Check for duplicate chain configuration.
    let mut unique_chain_ids = BTreeSet::new();
    for chain_id in config.chains.iter().map(|c| c.id.clone()) {
        if !unique_chain_ids.insert(chain_id.clone()) {
            return Diagnostic::DuplicateChains(chain_id);
        }
    }

    Diagnostic::Ok
}

impl Runnable for ValidateCmd {
    /// Validate the loaded configuration.
    fn run(&self) {
        let config = app_config();
        debug!("loaded configuration: {:#?}", *config);

        let diagnostic = validate_config(config);
        match diagnostic {
            Diagnostic::Ok => Output::success(format!("{}", diagnostic)).exit(),
            _ => Output::error(format!("{}", diagnostic)).exit(),
        }
    }
}
