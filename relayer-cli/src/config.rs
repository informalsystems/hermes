//! Cli Config
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use std::collections::BTreeSet;
use std::path::PathBuf;

use thiserror::Error;

use ibc::ics24_host::identifier::ChainId;
pub use ibc_relayer::config::Config;

use crate::application::app_reader;

/// Get the path to configuration file
pub fn config_path() -> Option<PathBuf> {
    let app = app_reader();
    app.config_path().cloned()
}

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
}

/// Method for syntactic validation of the input
/// configuration file.
pub fn validate_config(config: &Config) -> Result<(), Error> {
    // Check for duplicate chain configuration.
    let mut unique_chain_ids = BTreeSet::new();
    for chain_id in config.chains.iter().map(|c| c.id.clone()) {
        if !unique_chain_ids.insert(chain_id.clone()) {
            return Err(Error::DuplicateChains(chain_id));
        }
    }

    Ok(())
}
