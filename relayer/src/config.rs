//! Relayer configuration

use std::collections::HashSet;
use std::{fmt, fs, fs::File, io::Write, path::Path, time::Duration};

use serde_derive::{Deserialize, Serialize};
use tendermint_light_client::types::TrustThreshold;

use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::timestamp::ZERO_DURATION;

use crate::error;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GasPrice {
    pub price: f64,
    pub denom: String,
}

impl GasPrice {
    pub const fn new(price: f64, denom: String) -> Self {
        Self { price, denom }
    }
}

impl fmt::Display for GasPrice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.price, self.denom)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChainFilters {
    pub channels: HashSet<(PortId, ChannelId)>,
}

impl Default for ChainFilters {
    fn default() -> Self {
        Self {
            channels: HashSet::new(),
        }
    }
}

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
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    #[serde(default)]
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

/// Log levels are wrappers over [`tracing_core::Level`].
///
/// [`tracing_core::Level`]: https://docs.rs/tracing-core/0.1.17/tracing_core/struct.Level.html
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

impl Default for LogLevel {
    fn default() -> Self {
        Self::Info
    }
}

impl fmt::Display for LogLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LogLevel::Trace => write!(f, "trace"),
            LogLevel::Debug => write!(f, "debug"),
            LogLevel::Info => write!(f, "info"),
            LogLevel::Warn => write!(f, "warn"),
            LogLevel::Error => write!(f, "error"),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub struct GlobalConfig {
    pub strategy: Strategy,
    #[serde(default)]
    pub filter: bool,
    pub log_level: LogLevel,
    pub clear_packets_interval: u64,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            strategy: Strategy::default(),
            filter: false,
            log_level: LogLevel::default(),
            clear_packets_interval: 100,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
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
#[serde(deny_unknown_fields)]
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
    pub max_gas: Option<u64>,
    pub gas_adjustment: Option<f64>,
    pub max_msg_num: Option<usize>,
    pub max_tx_size: Option<usize>,
    #[serde(default = "default::clock_drift", with = "humantime_serde")]
    pub clock_drift: Duration,
    #[serde(default = "default::trusting_period", with = "humantime_serde")]
    pub trusting_period: Duration,

    // these two need to be last otherwise we run into `ValueAfterTable` error when serializing to TOML
    #[serde(default)]
    pub trust_threshold: TrustThreshold,
    pub gas_price: GasPrice,
    #[serde(default)]
    pub filters: ChainFilters,
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
    use test_env_log::test;

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
        store_writer(&config, &mut buffer).unwrap();
    }
}
