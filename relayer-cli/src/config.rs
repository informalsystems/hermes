//! Cli Config
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use std::collections::BTreeSet;

use thiserror::Error;

use ibc::ics24_host::identifier::ChainId;
pub use ibc_relayer::config::Config;

/// Specifies all the possible syntactic errors
/// that a Hermes configuration file could contain.
#[derive(Error, Debug)]
pub enum Error {
    /// No chain was configured
    #[error("config file does not specify any chain")]
    ZeroChains,

    /// The log level is invalid
    #[error("config file specifies an invalid log level ('{0}'), caused by: {1}")]
    InvalidLogLevel(String, String),

    /// Duplicate chains configured
    #[error("config file has duplicate entry for the chain with id {0}")]
    DuplicateChains(ChainId),
}

/// Validation method for syntactic validation of the input
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
