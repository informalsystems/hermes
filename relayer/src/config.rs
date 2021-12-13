//! Relayer configuration

mod error;
mod proof_specs;
pub mod reload;
pub mod types;

use alloc::collections::BTreeMap as HashMap;
use alloc::collections::BTreeSet as HashSet;
use core::{fmt, time::Duration};
use std::sync::{Arc, RwLock};
use std::{fs, fs::File, io::Write, path::Path};

use serde_derive::{Deserialize, Serialize};
use tendermint_light_client::types::TrustThreshold;

use ibc::core::ics23_commitment::specs::ProofSpecs;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::timestamp::ZERO_DURATION;

use crate::config::types::{MaxMsgNum, MaxTxSize, Memo};
use crate::keyring::Store;

pub use error::Error;

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
#[serde(
    rename_all = "lowercase",
    tag = "policy",
    content = "list",
    deny_unknown_fields
)]
pub enum PacketFilter {
    Allow(ChannelsSpec),
    Deny(ChannelsSpec),
    AllowAll,
}

impl Default for PacketFilter {
    /// By default, allows all channels & ports.
    fn default() -> Self {
        Self::AllowAll
    }
}

impl PacketFilter {
    /// Returns true if the packets can be relayed on the channel with [`PortId`] and [`ChannelId`],
    /// false otherwise.
    pub fn is_allowed(&self, port_id: &PortId, channel_id: &ChannelId) -> bool {
        match self {
            PacketFilter::Allow(spec) => spec.contains(&(port_id.clone(), channel_id.clone())),
            PacketFilter::Deny(spec) => !spec.contains(&(port_id.clone(), channel_id.clone())),
            PacketFilter::AllowAll => true,
        }
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ChannelsSpec(HashSet<(PortId, ChannelId)>);

impl ChannelsSpec {
    pub fn contains(&self, channel_port: &(PortId, ChannelId)) -> bool {
        self.0.contains(channel_port)
    }
}

/// Defaults for various fields
pub mod default {
    use super::*;

    pub fn tx_confirmation() -> bool {
        true
    }

    pub fn filter() -> bool {
        false
    }

    pub fn clear_packets_interval() -> u64 {
        100
    }

    pub fn rpc_timeout() -> Duration {
        Duration::from_secs(10)
    }

    pub fn clock_drift() -> Duration {
        Duration::from_secs(5)
    }

    pub fn max_block_time() -> Duration {
        Duration::from_secs(10)
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
    pub mode: ModeConfig,
    #[serde(default)]
    pub rest: RestConfig,
    #[serde(default)]
    pub telemetry: TelemetryConfig,
    #[serde(default = "Vec::new", skip_serializing_if = "Vec::is_empty")]
    pub chains: Vec<ChainConfig>,
}

pub type SharedConfig = Arc<RwLock<Config>>;

impl Config {
    pub fn has_chain(&self, id: &ChainId) -> bool {
        self.chains.iter().any(|c| c.id == *id)
    }

    pub fn find_chain(&self, id: &ChainId) -> Option<&ChainConfig> {
        self.chains.iter().find(|c| c.id == *id)
    }

    pub fn find_chain_mut(&mut self, id: &ChainId) -> Option<&mut ChainConfig> {
        self.chains.iter_mut().find(|c| c.id == *id)
    }

    /// Returns true if filtering is disabled or if packets are allowed on
    /// the channel [`PortId`] [`ChannelId`] on [`ChainId`].
    /// Returns false otherwise.
    pub fn packets_on_channel_allowed(
        &self,
        chain_id: &ChainId,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> bool {
        if !self.mode.packets.filter {
            return true;
        }

        match self.find_chain(chain_id) {
            None => false,
            Some(chain_config) => chain_config.packet_filter.is_allowed(port_id, channel_id),
        }
    }

    pub fn chains_map(&self) -> HashMap<&ChainId, &ChainConfig> {
        self.chains.iter().map(|c| (&c.id, c)).collect()
    }
}

#[derive(Copy, Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ModeConfig {
    pub clients: Clients,
    pub connections: Connections,
    pub channels: Channels,
    pub packets: Packets,
}

impl ModeConfig {
    pub fn all_disabled(&self) -> bool {
        !self.clients.enabled
            && !self.connections.enabled
            && !self.channels.enabled
            && !self.packets.enabled
    }
}

impl Default for ModeConfig {
    fn default() -> Self {
        Self {
            clients: Clients {
                enabled: true,
                refresh: true,
                misbehaviour: true,
            },
            connections: Connections { enabled: false },
            channels: Channels { enabled: false },
            packets: Packets {
                enabled: true,
                clear_interval: default::clear_packets_interval(),
                clear_on_start: true,
                filter: false,
                tx_confirmation: true,
            },
        }
    }
}

#[derive(Copy, Clone, Debug, Default, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Clients {
    pub enabled: bool,
    #[serde(default)]
    pub refresh: bool,
    #[serde(default)]
    pub misbehaviour: bool,
}

#[derive(Copy, Clone, Debug, Default, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Connections {
    pub enabled: bool,
}

#[derive(Copy, Clone, Debug, Default, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Channels {
    pub enabled: bool,
}

#[derive(Copy, Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Packets {
    pub enabled: bool,
    #[serde(default = "default::clear_packets_interval")]
    pub clear_interval: u64,
    #[serde(default)]
    pub clear_on_start: bool,
    #[serde(default = "default::filter")]
    pub filter: bool,
    #[serde(default = "default::tx_confirmation")]
    pub tx_confirmation: bool,
}

impl Default for Packets {
    fn default() -> Self {
        Self {
            enabled: false,
            clear_interval: default::clear_packets_interval(),
            clear_on_start: false,
            filter: default::filter(),
            tx_confirmation: default::tx_confirmation(),
        }
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

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub struct GlobalConfig {
    pub log_level: LogLevel,
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
pub struct RestConfig {
    pub enabled: bool,
    pub host: String,
    pub port: u16,
}

impl Default for RestConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            host: "127.0.0.1".to_string(),
            port: 3000,
        }
    }
}

/// It defines the address generation method
/// TODO: Ethermint `pk_type` to be restricted
/// after the Cosmos SDK release with ethsecp256k1
/// <https://github.com/cosmos/cosmos-sdk/pull/9981>
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(
    rename_all = "lowercase",
    tag = "derivation",
    content = "proto_type",
    deny_unknown_fields
)]
pub enum AddressType {
    Cosmos,
    Ethermint { pk_type: String },
}

impl Default for AddressType {
    fn default() -> Self {
        AddressType::Cosmos
    }
}

impl fmt::Display for AddressType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AddressType::Cosmos => write!(f, "cosmos"),
            AddressType::Ethermint { .. } => write!(f, "ethermint"),
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
    #[serde(default)]
    pub key_store_type: Store,
    pub store_prefix: String,
    pub default_gas: Option<u64>,
    pub max_gas: Option<u64>,
    pub gas_adjustment: Option<f64>,
    pub fee_granter: Option<String>,
    #[serde(default)]
    pub max_msg_num: MaxMsgNum,
    #[serde(default)]
    pub max_tx_size: MaxTxSize,
    #[serde(default = "default::clock_drift", with = "humantime_serde")]
    pub clock_drift: Duration,
    #[serde(default = "default::max_block_time", with = "humantime_serde")]
    pub max_block_time: Duration,
    #[serde(default, with = "humantime_serde")]
    pub trusting_period: Option<Duration>,
    #[serde(default)]
    pub memo_prefix: Memo,
    #[serde(default, with = "self::proof_specs")]
    pub proof_specs: ProofSpecs,

    // these two need to be last otherwise we run into `ValueAfterTable` error when serializing to TOML
    #[serde(default)]
    pub trust_threshold: TrustThreshold,
    pub gas_price: GasPrice,
    #[serde(default)]
    pub packet_filter: PacketFilter,
    #[serde(default)]
    pub address_type: AddressType,
}

/// Attempt to load and parse the TOML config file as a `Config`.
pub fn load(path: impl AsRef<Path>) -> Result<Config, Error> {
    let config_toml = std::fs::read_to_string(&path).map_err(Error::io)?;

    let config = toml::from_str::<Config>(&config_toml[..]).map_err(Error::decode)?;

    Ok(config)
}

/// Serialize the given `Config` as TOML to the given config file.
pub fn store(config: &Config, path: impl AsRef<Path>) -> Result<(), Error> {
    let mut file = if path.as_ref().exists() {
        fs::OpenOptions::new().write(true).truncate(true).open(path)
    } else {
        File::create(path)
    }
    .map_err(Error::io)?;

    store_writer(config, &mut file)
}

/// Serialize the given `Config` as TOML to the given writer.
pub(crate) fn store_writer(config: &Config, mut writer: impl Write) -> Result<(), Error> {
    let toml_config = toml::to_string_pretty(&config).map_err(Error::encode)?;

    writeln!(writer, "{}", toml_config).map_err(Error::io)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{load, store_writer};
    use test_log::test;

    #[test]
    fn parse_valid_config() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example.toml"
        );

        let config = load(path);
        println!("{:?}", config);
        assert!(config.is_ok());
    }

    #[test]
    fn serialize_valid_config() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example.toml"
        );

        let config = load(path).expect("could not parse config");

        let mut buffer = Vec::new();
        store_writer(&config, &mut buffer).unwrap();
    }
}
