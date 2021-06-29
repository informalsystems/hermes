//! Cli Config
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use std::collections::BTreeSet;

use flex_error::{define_error, TraceError};
use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::config::Config;
use tracing_subscriber::filter::ParseError;

// Specifies all the possible syntactic errors
// that a Hermes configuration file could contain.
define_error! {
    Error {
        ZeroChain
            |_| { "config file does not specify any chain" },

        InvalidLogLevel
            { log_level: String, }
            [ TraceError<ParseError> ]
            |e| {
                format!("config file specifies an invalid log level ('{0}'), caused by",
                    e.log_level)
            },

        DuplicateChains
            { chain_id: ChainId }
            |e| {
                format!("config file has duplicate entry for the chain with id {0}",
                    e.chain_id)
            },
    }
}

/// Method for syntactic validation of the input
/// configuration file.
pub fn validate_config(config: &Config) -> Result<(), Error> {
    // Check for duplicate chain configuration.
    let mut unique_chain_ids = BTreeSet::new();
    for chain_id in config.chains.iter().map(|c| c.id.clone()) {
        if !unique_chain_ids.insert(chain_id.clone()) {
            return Err(duplicate_chains_error(chain_id));
        }
    }

    Ok(())
}
