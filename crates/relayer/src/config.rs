//! Relayer configuration

pub mod error;
pub mod filter;
pub mod gas_multiplier;
pub mod proof_specs;
pub mod types;

use alloc::collections::BTreeMap;
use byte_unit::Byte;
use core::{
    cmp::Ordering,
    fmt::{Display, Error as FmtError, Formatter},
    str::FromStr,
    time::Duration,
};
use serde_derive::{Deserialize, Serialize};
use std::{
    fs,
    fs::File,
    io::Write,
    ops::Range,
    path::{Path, PathBuf},
};
use tendermint::block::Height as BlockHeight;
use tendermint_light_client::verifier::types::TrustThreshold;
use tendermint_rpc::client::CompatMode as TmCompatMode;
use tendermint_rpc::Url;
use tendermint_rpc::WebSocketClientUrl;

use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::core::ics23_commitment::specs::ProofSpecs;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer_types::timestamp::ZERO_DURATION;

use crate::chain::ChainType;
use crate::config::gas_multiplier::GasMultiplier;
use crate::config::types::{MaxMsgNum, MaxTxSize, Memo};
use crate::error::Error as RelayerError;
use crate::extension_options::ExtensionOptionDynamicFeeTx;
use crate::keyring::Store;

pub use crate::config::Error as ConfigError;
pub use error::Error;

pub use filter::PacketFilter;

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

impl Display for GasPrice {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}{}", self.price, self.denom)
    }
}

impl FromStr for GasPrice {
    type Err = ConfigError;

    fn from_str(price_in: &str) -> Result<Self, Self::Err> {
        // TODO: We split by `char::is_alphabetic` delimiter.
        //       More robust parsing methods might be needed.
        let spos = price_in.find(char::is_alphabetic);

        match spos {
            Some(position) => {
                let (price_str, denom) = price_in.split_at(position);

                let price = price_str
                    .parse::<f64>()
                    .map_err(|_| Error::invalid_gas_price(price_in.to_string()))?;

                Ok(GasPrice {
                    price,
                    denom: denom.to_owned(),
                })
            }

            None => Err(Error::invalid_gas_price(price_in.to_string())),
        }
    }
}

// Note: Only `PartialOrd` is implemented for `GasPrice` because gas
// prices must be of the same denomination in order to be compared.
impl PartialOrd for GasPrice {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.denom == other.denom {
            self.price.partial_cmp(&other.price)
        } else {
            None
        }
    }
}

/// Attempts to parse 0 or more `GasPrice`s from a String,
/// returning the successfully parsed prices in a Vec. Any
/// single price that fails to be parsed does not affect
/// the parsing of other prices.
pub fn parse_gas_prices(prices: String) -> Vec<GasPrice> {
    prices
        .split(';')
        .filter_map(|gp| GasPrice::from_str(gp).ok())
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    rename_all = "snake_case",
    tag = "type",
    content = "value",
    deny_unknown_fields
)]
pub enum ExtensionOption {
    EthermintDynamicFee(String),
}

impl ExtensionOption {
    pub fn to_any(&self) -> Result<Any, RelayerError> {
        match self {
            Self::EthermintDynamicFee(max_priority_price) => ExtensionOptionDynamicFeeTx {
                max_priority_price: max_priority_price.into(),
            }
            .to_any(),
        }
    }
}

impl Display for ExtensionOption {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            Self::EthermintDynamicFee(max_priority_price) => {
                write!(
                    f,
                    "EthermintDynamicFee(max_priority_price: {max_priority_price})"
                )
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum CompatMode {
    /// Use version 0.34 of the protocol.
    V0_34,
    /// Use version 0.37 of the protocol.
    V0_37,
}

impl Display for CompatMode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            Self::V0_34 => write!(f, "v0.34"),
            Self::V0_37 => write!(f, "v0.37"),
        }
    }
}

impl FromStr for CompatMode {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "V0_34" => Ok(Self::V0_34),
            "V0_37" => Ok(Self::V0_37),
            _ => Err(Error::invalid_compat_mode(s.to_owned())),
        }
    }
}

impl From<TmCompatMode> for CompatMode {
    fn from(value: TmCompatMode) -> Self {
        match value {
            TmCompatMode::V0_34 => Self::V0_34,
            TmCompatMode::V0_37 => Self::V0_37,
        }
    }
}

impl From<CompatMode> for TmCompatMode {
    fn from(value: CompatMode) -> Self {
        match value {
            CompatMode::V0_34 => Self::V0_34,
            CompatMode::V0_37 => Self::V0_37,
        }
    }
}

impl CompatMode {
    pub fn equal_to_tm_compat_mode(&self, tm_compat_mode: TmCompatMode) -> bool {
        match self {
            Self::V0_34 => tm_compat_mode == TmCompatMode::V0_34,
            Self::V0_37 => tm_compat_mode == TmCompatMode::V0_37,
        }
    }
}

/// Defaults for various fields
pub mod default {
    use super::*;

    pub fn chain_type() -> ChainType {
        ChainType::CosmosSdk
    }

    pub fn ccv_consumer_chain() -> bool {
        false
    }

    pub fn tx_confirmation() -> bool {
        false
    }

    pub fn clear_on_start() -> bool {
        true
    }

    pub fn clear_packets_interval() -> u64 {
        100
    }

    pub fn rpc_timeout() -> Duration {
        Duration::from_secs(10)
    }

    pub fn poll_interval() -> Duration {
        Duration::from_secs(1)
    }

    pub fn batch_delay() -> Duration {
        Duration::from_millis(500)
    }

    pub fn clock_drift() -> Duration {
        Duration::from_secs(5)
    }

    pub fn max_block_time() -> Duration {
        Duration::from_secs(30)
    }

    pub fn trusted_node() -> bool {
        false
    }

    pub fn connection_delay() -> Duration {
        ZERO_DURATION
    }

    pub fn auto_register_counterparty_payee() -> bool {
        false
    }

    pub fn max_grpc_decoding_size() -> Byte {
        Byte::from_bytes(33554432)
    }

    pub fn latency_submitted() -> HistogramConfig {
        HistogramConfig {
            range: Range {
                start: 500,
                end: 20000,
            },
            buckets: 10,
        }
    }

    pub fn latency_confirmed() -> HistogramConfig {
        HistogramConfig {
            range: Range {
                start: 1000,
                end: 30000,
            },
            buckets: 10,
        }
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
    #[serde(default)]
    pub tracing_server: TracingServerConfig,
}

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
        match self.find_chain(chain_id) {
            Some(chain_config) => chain_config
                .packet_filter
                .channel_policy
                .is_allowed(port_id, channel_id),
            None => false,
        }
    }

    pub fn chains_map(&self) -> BTreeMap<&ChainId, &ChainConfig> {
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

/// # IMPORTANT: Keep the values here in sync with the values in the default config.toml.
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
                ..Default::default()
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
    #[serde(default = "default::clear_on_start")]
    pub clear_on_start: bool,
    #[serde(default = "default::tx_confirmation")]
    pub tx_confirmation: bool,
    #[serde(default = "default::auto_register_counterparty_payee")]
    pub auto_register_counterparty_payee: bool,
}

impl Default for Packets {
    fn default() -> Self {
        Self {
            enabled: true,
            clear_interval: default::clear_packets_interval(),
            clear_on_start: default::clear_on_start(),
            tx_confirmation: default::tx_confirmation(),
            auto_register_counterparty_payee: default::auto_register_counterparty_payee(),
        }
    }
}

/// Log levels are wrappers over [`tracing_core::Level`].
///
/// [`tracing_core::Level`]: https://docs.rs/tracing-core/0.1.17/tracing_core/struct.Level.html
#[derive(Copy, Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
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

impl Display for LogLevel {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
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
    #[serde(default = "HistogramBuckets::default")]
    pub buckets: HistogramBuckets,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct HistogramBuckets {
    #[serde(default = "default::latency_submitted")]
    pub latency_submitted: HistogramConfig,
    #[serde(default = "default::latency_confirmed")]
    pub latency_confirmed: HistogramConfig,
}

impl Default for HistogramBuckets {
    fn default() -> Self {
        Self {
            latency_submitted: default::latency_submitted(),
            latency_confirmed: default::latency_confirmed(),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(try_from = "HistogramRangeUnchecked")]
pub struct HistogramConfig {
    #[serde(flatten)]
    pub range: Range<u64>,
    pub buckets: u64,
}

impl TryFrom<HistogramRangeUnchecked> for HistogramConfig {
    type Error = String;

    fn try_from(value: HistogramRangeUnchecked) -> Result<Self, Self::Error> {
        if value.start > value.end {
            return Err(format!(
                "histogram range min `{}` must be smaller or equal than max `{}`",
                value.start, value.end
            ));
        }
        Ok(Self {
            range: Range {
                start: value.start,
                end: value.end,
            },
            buckets: value.buckets,
        })
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct HistogramRangeUnchecked {
    start: u64,
    end: u64,
    buckets: u64,
}

/// Default values for the telemetry configuration.
///
/// # IMPORTANT: Remember to update the Hermes guide & the default config.toml whenever these values change.
impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            host: "127.0.0.1".to_string(),
            port: 3001,
            buckets: HistogramBuckets::default(),
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
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(
    rename_all = "lowercase",
    tag = "derivation",
    content = "proto_type",
    deny_unknown_fields
)]
#[derive(Default)]
pub enum AddressType {
    #[default]
    Cosmos,
    Ethermint {
        pk_type: String,
    },
}

impl Display for AddressType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            AddressType::Cosmos => write!(f, "cosmos"),
            AddressType::Ethermint { .. } => write!(f, "ethermint"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GenesisRestart {
    pub restart_height: BlockHeight,
    pub archive_addr: Url,
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(tag = "mode", rename_all = "lowercase")]
pub enum EventSourceMode {
    /// Push-based event source, via WebSocket
    Push {
        /// The WebSocket URL to connect to
        url: WebSocketClientUrl,

        /// Maximum amount of time to wait for a NewBlock event before emitting the event batch
        #[serde(default = "default::batch_delay", with = "humantime_serde")]
        batch_delay: Duration,
    },

    /// Pull-based event source, via RPC /block_results
    #[serde(alias = "poll")]
    Pull {
        /// The polling interval
        #[serde(default = "default::poll_interval", with = "humantime_serde")]
        interval: Duration,
    },
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ChainConfig {
    /// The chain's network identifier
    pub id: ChainId,

    /// The chain type
    #[serde(default = "default::chain_type")]
    pub r#type: ChainType,

    /// The RPC URL to connect to
    pub rpc_addr: Url,

    /// The gRPC URL to connect to
    pub grpc_addr: Url,

    /// The type of event source and associated settings
    pub event_source: EventSourceMode,

    /// Timeout used when issuing RPC queries
    #[serde(default = "default::rpc_timeout", with = "humantime_serde")]
    pub rpc_timeout: Duration,

    /// Whether or not the full node Hermes connects to is trusted
    #[serde(default = "default::trusted_node")]
    pub trusted_node: bool,

    pub account_prefix: String,
    pub key_name: String,
    #[serde(default)]
    pub key_store_type: Store,
    pub key_store_folder: Option<PathBuf>,
    pub store_prefix: String,
    pub default_gas: Option<u64>,
    pub max_gas: Option<u64>,

    // This field is only meant to be set via the `update client` command,
    // for when we need to ugprade a client across a genesis restart and
    // therefore need and archive node to fetch blocks from.
    pub genesis_restart: Option<GenesisRestart>,

    // This field is deprecated, use `gas_multiplier` instead
    pub gas_adjustment: Option<f64>,
    pub gas_multiplier: Option<GasMultiplier>,

    pub fee_granter: Option<String>,
    #[serde(default)]
    pub max_msg_num: MaxMsgNum,
    #[serde(default)]
    pub max_tx_size: MaxTxSize,
    #[serde(default = "default::max_grpc_decoding_size")]
    pub max_grpc_decoding_size: Byte,

    /// A correction parameter that helps deal with clocks that are only approximately synchronized
    /// between the source and destination chains for a client.
    /// This parameter is used when deciding to accept or reject a new header
    /// (originating from the source chain) for any client with the destination chain
    /// that uses this configuration, unless it is overridden by the client-specific
    /// clock drift option.
    #[serde(default = "default::clock_drift", with = "humantime_serde")]
    pub clock_drift: Duration,

    #[serde(default = "default::max_block_time", with = "humantime_serde")]
    pub max_block_time: Duration,

    /// The trusting period specifies how long a validator set is trusted for
    /// (must be shorter than the chain's unbonding period).
    #[serde(default, with = "humantime_serde")]
    pub trusting_period: Option<Duration>,

    /// CCV consumer chain
    #[serde(default = "default::ccv_consumer_chain")]
    pub ccv_consumer_chain: bool,

    #[serde(default)]
    pub memo_prefix: Memo,

    // This is an undocumented and hidden config to make the relayer wait for
    // DeliverTX before sending the next transaction when sending messages in
    // multiple batches. We will instruct relayer operators to turn this on
    // in case relaying failed in a chain with priority mempool enabled.
    // Warning: turning this on may cause degradation in performance.
    #[serde(default)]
    pub sequential_batch_tx: bool,

    // Note: These last few need to be last otherwise we run into `ValueAfterTable` error when serializing to TOML.
    //       That's because these are all tables and have to come last when serializing.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        with = "self::proof_specs"
    )]
    pub proof_specs: Option<ProofSpecs>,

    // These last few need to be last otherwise we run into `ValueAfterTable` error when serializing to TOML
    /// The trust threshold defines what fraction of the total voting power of a known
    /// and trusted validator set is sufficient for a commit to be accepted going forward.
    #[serde(default)]
    pub trust_threshold: TrustThreshold,

    pub gas_price: GasPrice,

    #[serde(default)]
    pub packet_filter: PacketFilter,

    #[serde(default)]
    pub address_type: AddressType,
    #[serde(default = "Vec::new", skip_serializing_if = "Vec::is_empty")]
    pub extension_options: Vec<ExtensionOption>,
    pub compat_mode: Option<CompatMode>,
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

    writeln!(writer, "{toml_config}").map_err(Error::io)?;

    Ok(())
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct TracingServerConfig {
    pub enabled: bool,
    pub port: u16,
}

impl Default for TracingServerConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            port: 5555,
        }
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::{load, parse_gas_prices, store_writer};
    use crate::config::GasPrice;
    use test_log::test;

    #[test]
    fn parse_valid_config() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example.toml"
        );

        let config = load(path).expect("could not parse config");

        dbg!(config);
    }

    #[test]
    fn parse_valid_fee_filter_config() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example_fee_filter.toml"
        );

        let config = load(path).expect("could not parse config");

        dbg!(config);
    }

    #[test]
    fn parse_valid_decoding_size_config() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example_decoding_size.toml"
        );

        let config = load(path).expect("could not parse config");

        dbg!(config);
    }

    #[test]
    fn parse_valid_telemetry() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example_valid_telemetry.toml"
        );

        let config = load(path).expect("could not parse config");

        dbg!(config);
    }

    #[test]
    fn parse_invalid_telemetry() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/config/fixtures/relayer_conf_example_invalid_telemetry.toml"
        );

        assert!(load(path).is_err());
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

    #[test]
    fn gas_price_from_str() {
        let gp_original = GasPrice::new(10.0, "atom".to_owned());

        let gp_raw = gp_original.to_string();
        let gp = GasPrice::from_str(&gp_raw).expect("could not parse String into GasPrice");

        assert_eq!(gp, gp_original);
    }

    #[test]
    fn parse_multiple_gas_prices() {
        let gas_prices = "0.25token1;0.0001token2";
        let parsed = parse_gas_prices(gas_prices.to_string());

        let expected = vec![
            GasPrice {
                price: 0.25,
                denom: "token1".to_owned(),
            },
            GasPrice {
                price: 0.0001,
                denom: "token2".to_owned(),
            },
        ];

        assert_eq!(expected, parsed);
    }

    #[test]
    fn parse_empty_gas_price() {
        let empty_price = "";
        let parsed = parse_gas_prices(empty_price.to_string());

        assert_eq!(parsed, vec![]);
    }

    #[test]
    fn malformed_gas_prices_do_not_get_parsed() {
        let malformed_prices = "token1;.token2;0.25token3";
        let parsed = parse_gas_prices(malformed_prices.to_string());

        let expected = vec![GasPrice {
            price: 0.25,
            denom: "token3".to_owned(),
        }];

        assert_eq!(expected, parsed);
    }
}
