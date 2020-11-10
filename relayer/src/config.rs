//! Read the relayer configuration into the Config struct, in examples for now
//! to support ADR validation..should move to relayer/src soon

use std::{
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
    pub grpc_addr: String,
    pub account_prefix: String,
    pub key_name: String,
    pub store_prefix: String,
    pub client_ids: Vec<String>,
    #[serde(default = "default::gas")]
    pub gas: u64,
    #[serde(default = "default::clock_drift", with = "humantime_serde")]
    pub clock_drift: Duration,
    #[serde(default = "default::trusting_period", with = "humantime_serde")]
    pub trusting_period: Duration,
    #[serde(default)]
    pub trust_threshold: TrustThreshold,

    // initially empty, to configure with the `light add/rm` commands
    #[serde(skip_serializing_if = "Option::is_none")]
    pub peers: Option<PeersConfig>,
}

impl ChainConfig {
    pub fn primary(&self) -> Option<&LightClientConfig> {
        let peers = self.peers.as_ref()?;
        peers.light_client(peers.primary)
    }

    pub fn light_client(&self, id: PeerId) -> Option<&LightClientConfig> {
        let peers = self.peers.as_ref()?;
        peers.light_client(id)
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
    pub light_clients: Vec<LightClientConfig>,
}

impl PeersConfig {
    pub fn light_client(&self, id: PeerId) -> Option<&LightClientConfig> {
        self.light_clients.iter().find(|p| p.peer_id == id)
    }

    pub fn light_client_mut(&mut self, id: PeerId) -> Option<&mut LightClientConfig> {
        self.light_clients.iter_mut().find(|p| p.peer_id == id)
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct LightClientConfig {
    pub peer_id: PeerId,
    pub address: net::Address,
    pub trusted_header_hash: Hash,
    pub trusted_height: Height,
}

/// Attempt to load and parse the TOML config file as a `Config`.
pub fn parse(path: impl AsRef<Path>) -> Result<Config, error::Error> {
    let config_toml =
        std::fs::read_to_string(&path).map_err(|e| error::Kind::ConfigIo.context(e))?;

    let config =
        toml::from_str::<Config>(&config_toml[..]).map_err(|e| error::Kind::Config.context(e))?;

    Ok(config)
}

/// Serialize the given `Config` as TOML to the given config file.
pub fn store(config: &Config, path: impl AsRef<Path>) -> Result<(), error::Error> {
    let mut file = File::create(path).map_err(|e| error::Kind::Config.context(e))?;
    store_writer(config, &mut file)
}

/// Serialize the given `Config` as TOML to the given writer.
pub(crate) fn store_writer(config: &Config, mut writer: impl Write) -> Result<(), error::Error> {
    let toml_config =
        toml::to_string_pretty(&config).map_err(|e| error::Kind::Config.context(e))?;

    writeln!(writer, "{}", toml_config).map_err(|e| error::Kind::Config.context(e))?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{parse, store_writer};

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

    #[test]
    fn serialize_valid_config() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example.toml"
        );

        let config = parse(path).expect("could not parse config");
        let mut buffer = Vec::new();

        let result = store_writer(&config, &mut buffer);
        assert!(result.is_ok());
    }
}
