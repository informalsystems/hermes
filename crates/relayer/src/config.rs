//! Relayer configuration

pub mod compat_mode;
pub mod error;
pub mod filter;
pub mod gas_multiplier;
pub mod proof_specs;
pub mod types;

use alloc::collections::BTreeMap;
use core::{
    cmp::Ordering,
    fmt::{
        Display,
        Error as FmtError,
        Formatter,
    },
    str::FromStr,
    time::Duration,
};
use std::{
    fs,
    fs::File,
    io::Write,
    ops::Range,
    path::Path,
};

use byte_unit::Byte;
pub use error::Error;
pub use filter::PacketFilter;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::{
    core::{
        ics23_commitment::specs::ProofSpecs,
        ics24_host::identifier::{
            ChainId,
            ChannelId,
            PortId,
        },
    },
    timestamp::ZERO_DURATION,
};
use serde_derive::{
    Deserialize,
    Serialize,
};
use tendermint::block::Height as BlockHeight;
use tendermint_rpc::{
    Url,
    WebSocketClientUrl,
};

pub use crate::config::Error as ConfigError;
use crate::{
    chain::cosmos::config::CosmosSdkConfig,
    error::Error as RelayerError,
    extension_options::ExtensionOptionDynamicFeeTx,
    keyring,
    keyring::{
        AnySigningKeyPair,
        KeyRing,
        Store,
    },
};

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

/// Defaults for various fields
pub mod default {
    use super::*;

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
        Duration::from_secs(60)
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
        self.chains.iter().any(|c| c.id() == id)
    }

    pub fn find_chain(&self, id: &ChainId) -> Option<&ChainConfig> {
        self.chains.iter().find(|c| c.id() == id)
    }

    pub fn find_chain_mut(&mut self, id: &ChainId) -> Option<&mut ChainConfig> {
        self.chains.iter_mut().find(|c| c.id() == id)
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
                .packet_filter()
                .channel_policy
                .is_allowed(port_id, channel_id),
            None => false,
        }
    }

    pub fn chains_map(&self) -> BTreeMap<&ChainId, &ChainConfig> {
        self.chains.iter().map(|c| (c.id(), c)).collect()
    }

    /// Method for syntactic validation of the input configuration file.
    pub fn validate_config(&self) -> Result<(), Diagnostic<Error>> {
        use alloc::collections::BTreeSet;
        // Check for duplicate chain configuration and invalid trust thresholds
        let mut unique_chain_ids = BTreeSet::new();
        for chain_config in self.chains.iter() {
            let already_present = !unique_chain_ids.insert(chain_config.id().clone());
            if already_present {
                return Err(Diagnostic::Error(Error::duplicate_chains(
                    chain_config.id().clone(),
                )));
            }

            match chain_config {
                ChainConfig::CosmosSdk(config) => {
                    config.validate().map_err(Into::<Diagnostic<Error>>::into)?;
                }
                ChainConfig::Astria(config) => {
                    config.validate().map_err(Into::<Diagnostic<Error>>::into)?;
                }
            }
        }

        // Check for invalid mode config
        self.mode.validate()?;

        Ok(())
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

    fn validate(&self) -> Result<(), Diagnostic<Error>> {
        if self.all_disabled() {
            return Err(Diagnostic::Warning(Error::invalid_mode(
                "all operation modes of Hermes are disabled, relayer won't perform any action aside from subscribing to events".to_string(),
            )));
        }

        if self.clients.enabled && !self.clients.refresh && !self.clients.misbehaviour {
            return Err(Diagnostic::Error(Error::invalid_mode(
                "either `refresh` or `misbehaviour` must be set to true if `clients.enabled` is set to true".to_string(),
            )));
        }

        Ok(())
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
    Cosmos, // secp256k1?
    Ethermint {
        pk_type: String,
    },
    Astria, // ed25519
}

impl Display for AddressType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            AddressType::Cosmos => write!(f, "cosmos"),
            AddressType::Ethermint { .. } => write!(f, "ethermint"),
            AddressType::Astria => write!(f, "astria"),
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
#[serde(tag = "type")]
pub enum ChainConfig {
    CosmosSdk(CosmosSdkConfig),
    Astria(CosmosSdkConfig), // TODO: if the config is the cometbft config, it's the same
}

impl ChainConfig {
    pub fn id(&self) -> &ChainId {
        match self {
            Self::CosmosSdk(config) => &config.id,
            Self::Astria(config) => &config.id,
        }
    }

    pub fn rpc_addr(&self) -> &Url {
        match self {
            Self::CosmosSdk(config) => &config.rpc_addr,
            Self::Astria(config) => &config.rpc_addr,
        }
    }

    pub fn packet_filter(&self) -> &PacketFilter {
        match self {
            Self::CosmosSdk(config) => &config.packet_filter,
            Self::Astria(config) => &config.packet_filter,
        }
    }

    pub fn max_block_time(&self) -> Duration {
        match self {
            Self::CosmosSdk(config) => config.max_block_time,
            Self::Astria(config) => config.max_block_time,
        }
    }

    pub fn key_name(&self) -> &String {
        match self {
            Self::CosmosSdk(config) => &config.key_name,
            Self::Astria(config) => &config.key_name,
        }
    }

    pub fn set_key_name(&mut self, key_name: String) {
        match self {
            Self::CosmosSdk(config) => config.key_name = key_name,
            Self::Astria(config) => config.key_name = key_name,
        }
    }

    pub fn list_keys(&self) -> Result<Vec<(String, AnySigningKeyPair)>, keyring::errors::Error> {
        let keys = match self {
            ChainConfig::CosmosSdk(config) => {
                let keyring = KeyRing::new_secp256k1(
                    Store::Test,
                    &config.account_prefix,
                    &config.id,
                    &config.key_store_folder,
                )?;
                keyring
                    .keys()?
                    .into_iter()
                    .map(|(key_name, keys)| (key_name, keys.into()))
                    .collect()
            }
            ChainConfig::Astria(config) => {
                let keyring = KeyRing::new_ed25519(
                    Store::Test,
                    &config.account_prefix,
                    &config.id,
                    &config.key_store_folder,
                )?;
                keyring
                    .keys()?
                    .into_iter()
                    .map(|(key_name, keys)| (key_name, keys.into()))
                    .collect()
            }
        };
        Ok(keys)
    }

    pub fn clear_interval(&self) -> Option<u64> {
        match self {
            Self::CosmosSdk(config) => config.clear_interval,
            Self::Astria(config) => config.clear_interval,
        }
    }

    pub fn max_grpc_decoding_size(&self) -> Byte {
        match self {
            Self::CosmosSdk(config) => config.max_grpc_decoding_size,
            Self::Astria(config) => config.max_grpc_decoding_size,
        }
    }

    pub fn proof_specs(&self) -> &Option<ProofSpecs> {
        match self {
            Self::CosmosSdk(config) => &config.proof_specs,
            Self::Astria(config) => &config.proof_specs,
        }
    }

    pub fn event_source_mode(&self) -> &EventSourceMode {
        match self {
            Self::CosmosSdk(config) => &config.event_source,
            Self::Astria(config) => &config.event_source,
        }
    }
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

#[derive(Clone, Debug)]
pub enum Diagnostic<E> {
    Warning(E),
    Error(E),
}

use crate::chain::cosmos::config::Diagnostic as CosmosConfigDiagnostic;
impl<E: Into<Error>> From<CosmosConfigDiagnostic<E>> for Diagnostic<Error> {
    fn from(value: CosmosConfigDiagnostic<E>) -> Self {
        match value {
            CosmosConfigDiagnostic::Warning(e) => Diagnostic::Warning(e.into()),
            CosmosConfigDiagnostic::Error(e) => Diagnostic::Error(e.into()),
        }
    }
}

use crate::chain::cosmos::config::error::Error as CosmosConfigError;
impl From<CosmosConfigError> for Error {
    fn from(error: CosmosConfigError) -> Error {
        Error::cosmos_config_error(error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use test_log::test;

    use super::{
        load,
        parse_gas_prices,
        store_writer,
    };
    use crate::config::GasPrice;

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
