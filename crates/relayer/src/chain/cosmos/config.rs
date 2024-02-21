use core::time::Duration;
use std::path::PathBuf;

use byte_unit::Byte;
use serde_derive::{Deserialize, Serialize};
use tendermint_rpc::Url;

use ibc_relayer_types::core::ics23_commitment::specs::ProofSpecs;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::chain::cosmos::config::error::Error as ConfigError;
use crate::config::compat_mode::CompatMode;
use crate::config::dynamic_gas::DynamicGasPrice;
use crate::config::gas_multiplier::GasMultiplier;
use crate::config::types::{MaxMsgNum, MaxTxSize, Memo, TrustThreshold};
use crate::config::{
    self, AddressType, EventSourceMode, ExtensionOption, GasPrice, GenesisRestart, PacketFilter,
};
use crate::config::{default, RefreshRate};
use crate::keyring::Store;

pub mod error;

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CosmosSdkConfig {
    /// The chain's network identifier
    pub id: ChainId,

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

    /// How many packets to fetch at once from the chain when clearing packets
    #[serde(default = "default::query_packets_chunk_size")]
    pub query_packets_chunk_size: usize,

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

    /// The rate at which to refresh the client referencing this chain,
    /// expressed as a fraction of the trusting period.
    #[serde(default = "default::client_refresh_rate")]
    pub client_refresh_rate: RefreshRate,

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
        with = "config::proof_specs"
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
    pub dynamic_gas_price: DynamicGasPrice,

    #[serde(default)]
    pub address_type: AddressType,
    #[serde(default = "Vec::new", skip_serializing_if = "Vec::is_empty")]
    pub extension_options: Vec<ExtensionOption>,
    pub compat_mode: Option<CompatMode>,
    pub clear_interval: Option<u64>,
}

impl CosmosSdkConfig {
    pub fn validate(&self) -> Result<(), Diagnostic<ConfigError>> {
        validate_trust_threshold(&self.id, self.trust_threshold)?;
        validate_gas_settings(&self.id, self.gas_adjustment)?;
        Ok(())
    }
}

/// Check that the trust threshold is:
///
/// a) non-zero
/// b) greater or equal to 1/3
/// c) strictly less than 1
pub fn validate_trust_threshold(
    id: &ChainId,
    trust_threshold: TrustThreshold,
) -> Result<(), Diagnostic<ConfigError>> {
    if trust_threshold.denominator() == 0 {
        return Err(Diagnostic::Error(ConfigError::invalid_trust_threshold(
            trust_threshold,
            id.clone(),
            "trust threshold denominator cannot be zero".to_string(),
        )));
    }

    if trust_threshold.numerator() * 3 < trust_threshold.denominator() {
        return Err(Diagnostic::Error(ConfigError::invalid_trust_threshold(
            trust_threshold,
            id.clone(),
            "trust threshold cannot be < 1/3".to_string(),
        )));
    }

    if trust_threshold.numerator() >= trust_threshold.denominator() {
        return Err(Diagnostic::Error(ConfigError::invalid_trust_threshold(
            trust_threshold,
            id.clone(),
            "trust threshold cannot be >= 1".to_string(),
        )));
    }

    Ok(())
}

fn validate_gas_settings(
    id: &ChainId,
    gas_adjustment: Option<f64>,
) -> Result<(), Diagnostic<ConfigError>> {
    // Check that the gas_adjustment option is not set
    if let Some(gas_adjustment) = gas_adjustment {
        let gas_multiplier = gas_adjustment + 1.0;

        return Err(Diagnostic::Error(ConfigError::deprecated_gas_adjustment(
            gas_adjustment,
            gas_multiplier,
            id.clone(),
        )));
    }

    Ok(())
}
#[derive(Clone, Debug)]
pub enum Diagnostic<E> {
    Warning(E),
    Error(E),
}
