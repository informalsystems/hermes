//! Read the relayer configuration into the Config struct, in examples for now
//! to support ADR validation..should move to relayer/src soon

use serde_derive::{Deserialize, Serialize};
use std::path::Path;

use crate::error;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Config {
    pub timeout: Option<String>,  // use "10s" as default
    pub strategy: Option<String>, // use "naive" as default
    pub chains: Vec<ChainConfig>,
    pub connections: Option<Vec<Connection>>, // use all for default
}

impl Default for Config {
    fn default() -> Self {
        Self {
            timeout: Some("10s".to_string()),
            strategy: Some("naive".to_string()),
            chains: vec![],
            connections: None,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ChainConfig {
    pub id: String,
    pub rpc_addr: Option<String>, // use "http://localhost:26657" as default
    pub account_prefix: String,
    pub key_name: String,
    pub client_ids: Vec<String>,
    pub gas: Option<u64>, // use 200000 as default
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Connection {
    pub src: Option<ConnectionEnd>,    // use any source
    pub dest: Option<ConnectionEnd>,   // use any destination
    pub paths: Option<Vec<RelayPath>>, // use any port, direction bidirectional
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ConnectionEnd {
    pub client_id: String,
    pub connection_id: Option<String>, // use all connections to this client
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RelayPath {
    pub src_port: Option<String>,  // default from any source port
    pub dest_port: Option<String>, // default from any dest port
    pub direction: Option<String>, // default bidirectional
}

/// Attempt to load and parse the config file into the Config struct.
///
/// TODO: If a file cannot be found, return a default Config allowing relayer
///       to relay everything from any to any chain(?)
pub fn parse(path: impl AsRef<Path>) -> Result<Config, error::Error> {
    let config_toml =
        std::fs::read_to_string(&path).map_err(|e| error::Kind::ConfigIo.context(e))?;

    let config =
        toml::from_str::<Config>(&config_toml[..]).map_err(|e| error::Kind::Config.context(e))?;

    Ok(config)
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn parse_valid_config() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example.toml"
        );

        let config = parse(path);
        assert!(config.is_ok());
    }
}
