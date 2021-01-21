//! Read the relayer configuration into the Config struct, in examples for now
//! to support ADR validation..should move to relayer/src soon

use std::{
    fs,
    fs::File,
    io::Write,
    path::{Path, PathBuf},
    time::Duration,
};

use serde_derive::{Deserialize, Serialize};
use tendermint::{net, Hash};
use tendermint_light_client::types::{Height, PeerId, TrustThreshold};

use ibc::ics24_host::identifier::{ChainId, PortId};

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

impl Config {
    pub fn find_chain(&self, id: &ChainId) -> Option<&ChainConfig> {
        self.chains.iter().find(|c| c.id == *id)
    }

    pub fn find_chain_mut(&mut self, id: &ChainId) -> Option<&mut ChainConfig> {
        self.chains.iter_mut().find(|c| c.id == *id)
    }
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

    /// All valid log levels, as defined in tracing:
    /// https://docs.rs/tracing-core/0.1.17/tracing_core/struct.Level.html
    pub log_level: String,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            timeout: default::timeout(),
            strategy: Strategy::default(),
            log_level: "info".to_string(),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ChainConfig {
    pub id: ChainId,
    #[serde(default = "default::rpc_addr")]
    pub rpc_addr: net::Address,
    pub grpc_addr: String,
    pub account_prefix: String,
    pub key_name: String,
    pub store_prefix: String,
    pub gas: Option<u64>,
    pub max_msg_num: Option<usize>,
    pub max_tx_size: Option<usize>,
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

    pub fn witnesses(&self) -> Option<Vec<&LightClientConfig>> {
        let peers = self.peers.as_ref()?;

        Some(
            peers
                .light_clients
                .iter()
                .filter(|p| p.peer_id != peers.primary)
                .collect(),
        )
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Connection {
    pub a_chain: ChainId,
    pub b_chain: ChainId,
    pub paths: Option<Vec<RelayPath>>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RelayPath {
    pub a_port: PortId,
    pub b_port: PortId,
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
    #[serde(default = "default::timeout", with = "humantime_serde")]
    pub timeout: Duration,
    pub trusted_header_hash: Hash,
    pub trusted_height: Height,
    pub store: StoreConfig,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum StoreConfig {
    #[serde(rename = "disk")]
    Disk { path: PathBuf },
    #[serde(rename = "memory")]
    Memory {
        #[serde(skip)]
        dummy: (),
    },
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
    let mut file = if path.as_ref().exists() {
        fs::OpenOptions::new().write(true).truncate(true).open(path)
    } else {
        File::create(path)
    }
    .map_err(|e| error::Kind::Config.context(e))?;

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
