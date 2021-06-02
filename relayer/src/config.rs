//! Relayer configuration

use std::{fs, fs::File, io::Write, path::Path, time::Duration};

use serde_derive::{Deserialize, Serialize};
use tendermint_light_client::types::TrustThreshold;

use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::ChainId;
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
    #[serde(default)]
    pub telemetry: TelemetryConfig,
    #[serde(default = "Vec::new", skip_serializing_if = "Vec::is_empty")]
    pub chains: Vec<ChainConfig>,
}

impl Config {
    pub fn find_chain(&self, id: &ChainId) -> Option<&ChainConfig> {
        self.chains.iter().find(|c| c.id == *id)
    }

    pub fn find_chain_mut(&mut self, id: &ChainId) -> Option<&mut ChainConfig> {
        self.chains.iter_mut().find(|c| c.id == *id)
    }
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum Strategy {
    #[serde(rename = "packets")]
    Packets,

    #[serde(rename = "all")]
    HandshakeAndPackets,
}

impl Default for Strategy {
    fn default() -> Self {
        Self::Packets
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct GlobalConfig {
    #[serde(default)]
    pub strategy: Strategy,

    /// All valid log levels, as defined in tracing:
    /// https://docs.rs/tracing-core/0.1.17/tracing_core/struct.Level.html
    pub log_level: String,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            strategy: Strategy::default(),
            log_level: "info".to_string(),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct TelemetryConfig {
    pub enabled: bool,
    pub host: String,
    pub port: u16,
}

impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            host: "127.0.0.1".to_string(),
            port: 3001,
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
