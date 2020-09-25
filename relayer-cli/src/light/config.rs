//! Light client configuration

use std::collections::HashMap;
use std::fs;
use std::path::Path;

use serde_derive::{Deserialize, Serialize};

use relayer::client::TrustOptions;
use tendermint::chain;

use crate::error;

/// Default path for the light command config file
pub const LIGHT_CONFIG_PATH: &str = "light_config.toml";

/// Light client configuration, as set by the `light init` command.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LightConfig {
    /// Mapping from chain identifier to trust options
    pub chains: HashMap<chain::Id, TrustOptions>,
}

impl LightConfig {
    /// Load the configuration from a TOML file at `path`, or return the empty
    /// config if the file does not exists.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, error::Error> {
        let config = match fs::read_to_string(path) {
            Ok(contents) => {
                toml::from_str(&contents).map_err(|e| error::Kind::Config.context(e))?
            }
            Err(_) => LightConfig {
                chains: HashMap::new(),
            },
        };

        Ok(config)
    }

    /// Save the configuration to a TOML file at `path`
    pub fn save(&self, path: impl AsRef<Path>) -> Result<(), error::Error> {
        let contents = toml::to_string_pretty(self).map_err(|e| error::Kind::Config.context(e))?;
        fs::write(path, contents).map_err(|e| error::Kind::Config.context(e))?;

        Ok(())
    }
}
