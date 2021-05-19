//! Relayer configuration

use std::{fs, fs::File, io::Write, path::Path, time::Duration};

use serde_derive::{Deserialize, Serialize};
use tendermint_light_client::types::TrustThreshold;

use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChainId, PortId};
use ibc::timestamp::ZERO_DURATION;

use crate::error;

/// Defaults for various fields
pub mod default {
    use super::*;

    pub fn rpc_timeout() -> Duration {
        Duration::from_secs(10)
    }

    pub fn trusting_period() -> Duration {
        Duration::from_secs(336 * 60 * 60) // 336 hours ~ 14 days
    }

    pub fn clock_drift() -> Duration {
        Duration::from_secs(5)
    }

    pub fn connection_delay() -> Duration {
        ZERO_DURATION
    }

    pub fn channel_ordering() -> Order {
        Order::Unordered
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

    pub fn first_matching_path(
        &self,
        src_chain: &ChainId,
        dst_chain: &ChainId,
    ) -> Option<(&Connection, &RelayPath)> {
        let connection = self.connections.as_ref()?.iter().find(|c| {
            c.a_chain == *src_chain && c.b_chain == *dst_chain
                || c.a_chain == *dst_chain && c.b_chain == *src_chain
        });

        connection.and_then(|conn| conn.paths.as_ref().map(|paths| (conn, &paths[0])))
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
    #[serde(default)]
    pub strategy: Strategy,

    /// All valid log levels, as defined in tracing:
    /// https://docs.rs/tracing-core/0.1.17/tracing_core/struct.Level.html
    pub log_level: String,

    /// REST interface address
    pub rest_addr: String,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            strategy: Strategy::default(),
            log_level: "info".to_string(),
            rest_addr: "127.0.0.1:9999".to_string(),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ChainConfig {
    pub id: ChainId,
    pub rpc_addr: tendermint_rpc::Url,
    pub websocket_addr: tendermint_rpc::Url,
    pub grpc_addr: tendermint_rpc::Url,
    #[serde(default = "default::rpc_timeout", with = "humantime_serde")]
    pub rpc_timeout: Duration,
    pub account_prefix: String,
    pub key_name: String,
    pub store_prefix: String,
    pub gas: Option<u64>,
    pub fee_denom: String,
    pub fee_amount: Option<u64>,
    pub max_msg_num: Option<usize>,
    pub max_tx_size: Option<usize>,
    #[serde(default = "default::clock_drift", with = "humantime_serde")]
    pub clock_drift: Duration,
    #[serde(default = "default::trusting_period", with = "humantime_serde")]
    pub trusting_period: Duration,
    #[serde(default)]
    pub trust_threshold: TrustThreshold,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Connection {
    pub a_chain: ChainId,
    pub b_chain: ChainId,
    #[serde(default = "default::connection_delay", with = "humantime_serde")]
    pub delay: Duration,
    pub paths: Option<Vec<RelayPath>>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RelayPath {
    pub a_port: PortId,
    pub b_port: PortId,
    #[serde(default = "default::channel_ordering")]
    pub ordering: Order,
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
