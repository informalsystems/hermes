//! Read the relayer configuration into the Config struct, in examples for now
//! to support ADR validation..should move to relayer/src soon

use std::{
    collections::HashMap,
    fs::File,
    io::Write,
    path::{Path, PathBuf},
    time::Duration,
};

use serde_derive::{Deserialize, Serialize};

use tendermint::{chain, net, node, Hash};
use tendermint_light_client::types::{Height, PeerId, TrustThreshold};

use crate::error;

/// Defaults for various fields
pub mod default {
    use super::*;

    pub fn timeout() -> Duration {
        Duration::from_secs(10)
    }

    pub fn gas() -> u64 {
        200_000
    }

    pub fn rpc_addr() -> net::Address {
        "localhost:26657".parse().unwrap()
    }

    pub fn trusting_period() -> Duration {
        Duration::from_secs(336 * 60 * 60) // 336 hours
    }

    pub fn clock_drift() -> Duration {
        Duration::from_secs(5) // 5 seconds
    }
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct Config {
    pub global: GlobalConfig,
    #[serde(default = "Vec::new", skip_serializing_if = "Vec::is_empty")]
    pub chains: Vec<ChainConfig>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub connections: Option<Vec<Connection>>, // use all for default
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Strategy {
    #[serde(rename = "naive")]
    Naive,
}

impl Default for Strategy {
    fn default() -> Self {
        Self::Naive
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct GlobalConfig {
    #[serde(default = "default::timeout", with = "humantime_serde")]
    pub timeout: Duration,
    #[serde(default)]
    pub strategy: Strategy,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            timeout: default::timeout(),
            strategy: Strategy::default(),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ChainConfig {
    pub id: chain::Id,
    #[serde(default = "default::rpc_addr")]
    pub rpc_addr: net::Address,
    pub account_prefix: String,
    pub key_name: String,
    pub store_prefix: String,
    pub client_ids: Vec<String>,
    #[serde(default = "default::gas")]
    pub gas: u64,

    #[serde(default)]
    pub trust_threshold: TrustThreshold,
    #[serde(default = "default::clock_drift", with = "humantime_serde")]
    pub clock_drift: Duration,
    #[serde(default = "default::trusting_period", with = "humantime_serde")]
    pub trusting_period: Duration,

    pub peers: Option<PeersConfig>, // initially empty, to configure with the `light add/rm` commands
}

impl ChainConfig {
    pub fn primary(&self) -> Option<&LightClientConfig> {
        let peers = self.peers.as_ref()?;
        peers.peer(peers.primary)
    }

    pub fn peer(&self, id: PeerId) -> Option<&LightClientConfig> {
        let peers = self.peers.as_ref()?;
        peers.peer(id)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Connection {
    pub src: Option<ConnectionEnd>,    // use any source
    pub dest: Option<ConnectionEnd>,   // use any destination
    pub paths: Option<Vec<RelayPath>>, // use any port, direction bidirectional
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ConnectionEnd {
    pub chain_id: String,
    pub client_id: String,
    pub connection_id: Option<String>, // use all connections to this client
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Direction {
    #[serde(rename = "unidirectional")]
    Unidirectional,
    #[serde(rename = "bidirectional")]
    Bidirectional,
}

impl Default for Direction {
    fn default() -> Self {
        Self::Bidirectional
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RelayPath {
    pub src_port: Option<String>,     // default from any source port
    pub dest_port: Option<String>,    // default from any dest port
    pub src_channel: Option<String>,  // default from any source port
    pub dest_channel: Option<String>, // default from any dest port
    #[serde(default)]
    pub direction: Direction, // default bidirectional
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PeersConfig {
    pub primary: PeerId,
    pub peers: Vec<LightClientConfig>,
}

impl PeersConfig {
    pub fn peer(&self, id: PeerId) -> Option<&LightClientConfig> {
        self.peers.iter().find(|p| p.peer_id == id)
    }

    pub fn peer_mut(&mut self, id: PeerId) -> Option<&mut LightClientConfig> {
        self.peers.iter_mut().find(|p| p.peer_id == id)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct LightClientConfig {
    pub peer_id: PeerId,
    pub address: net::Address,
    pub trusted_header_hash: Hash,
    pub trusted_height: Height,
}

/// Attempt to load and parse the config file into the Config struct.
pub fn parse(path: impl AsRef<Path>) -> Result<Config, error::Error> {
    let config_toml =
        std::fs::read_to_string(&path).map_err(|e| error::Kind::ConfigIo.context(e))?;

    let config =
        toml::from_str::<Config>(&config_toml[..]).map_err(|e| error::Kind::Config.context(e))?;

    Ok(config)
}

/// Attempt to serialize and store a Config in the given config file.
pub fn store(config: &Config, path: impl AsRef<Path>) -> Result<(), error::Error> {
    // This is a workaround to ensure that we can serialize the configuration without
    // running into the dreaded 'values must be emitted before tables' TOML error.
    // See https://github.com/alexcrichton/toml-rs/issues/142
    let toml_value = toml::Value::try_from(config).map_err(|e| error::Kind::Config.context(e))?;

    let toml_config =
        toml::to_string_pretty(&toml_value).map_err(|e| error::Kind::Config.context(e))?;

    let mut file = File::create(path).map_err(|e| error::Kind::Config.context(e))?;
    writeln!(file, "{}", toml_config).map_err(|e| error::Kind::Config.context(e))?;

    Ok(())
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
        println!("{:?}", config);
        assert!(config.is_ok());
    }
}