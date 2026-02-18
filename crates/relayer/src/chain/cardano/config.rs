//! Configuration for Cardano chain

use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::time::Duration;

use crate::config::{default, PacketFilter, RefreshRate};
use crate::keyring::Store;

/// Minimal configuration for Cardano chain integration
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CardanoConfig {
    /// The chain's network identifier
    pub id: ChainId,

    /// Gateway gRPC endpoint URL
    pub gateway_url: String,

    /// Network ID (1 = mainnet, 0 = testnet)
    pub network_id: u8,

    /// Key name for signing
    pub key_name: String,

    /// Keystore type (test, file, etc.)
    #[serde(default)]
    pub key_store_type: Store,

    /// Optional path to keystore folder
    pub key_store_folder: Option<PathBuf>,

    /// Account index for CIP-1852 derivation
    #[serde(default)]
    pub account: u32,

    /// Maximum block time (for timeout calculations)
    #[serde(default = "default_max_block_time", with = "humantime_serde")]
    pub max_block_time: Duration,

    /// Packet filter configuration
    #[serde(default)]
    pub packet_filter: PacketFilter,

    /// Optional trust threshold (not used by Cardano but required by config interface)
    #[serde(default)]
    pub trust_threshold:
        Option<ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold>,

    /// How many packets to fetch at once from the chain when clearing packets
    #[serde(default = "default_query_packets_chunk_size")]
    pub query_packets_chunk_size: usize,

    /// Optional clear interval
    pub clear_interval: Option<u64>,

    /// Clock drift tolerance
    #[serde(default = "default_clock_drift", with = "humantime_serde")]
    pub clock_drift: Duration,

    /// The rate at which to refresh the client referencing this chain,
    /// expressed as a fraction of the trusting period.
    #[serde(default = "default::client_refresh_rate")]
    pub client_refresh_rate: RefreshRate,

    /// Event polling interval for monitoring IBC events
    #[serde(default = "default_event_poll_interval", with = "humantime_serde")]
    pub event_poll_interval: Option<Duration>,

    /// Maximum amount of time Hermes will wait after a Cardano transaction is included
    /// until it is also "Mithril-certified".
    ///
    /// Important nuance about "height":
    /// In this Cardano↔Cosmos integration, `Height.revision_height` is treated as a Cardano
    /// *block number* (as surfaced by `db-sync` and by Mithril's `cardano-transactions`
    /// snapshots). It is not a Cardano *slot number*.
    ///
    /// When Hermes submits a transaction on Cardano, the Gateway returns the inclusion
    /// block number. Hermes then waits until the Gateway reports a Mithril snapshot
    /// whose `block_number` is >= that inclusion block number, before proceeding to the
    /// next IBC step. Without this, Hermes can race ahead and build proofs at a height
    /// that the Cosmos-side Mithril light client cannot yet verify.
    #[serde(
        default = "default_mithril_certification_timeout",
        with = "humantime_serde"
    )]
    pub mithril_certification_timeout: Duration,

    /// Polling interval while waiting for Mithril snapshots to catch up.
    #[serde(default = "default_mithril_poll_interval", with = "humantime_serde")]
    pub mithril_poll_interval: Duration,

    /// How often to log progress while waiting for Mithril snapshot catch-up.
    ///
    /// This is intentionally an `INFO`-level log, because in many environments the default
    /// log level is `info` (so `debug` would be invisible and the process would look hung).
    #[serde(
        default = "default_mithril_wait_log_interval",
        with = "humantime_serde"
    )]
    pub mithril_wait_log_interval: Duration,
}

fn default_max_block_time() -> Duration {
    Duration::from_secs(30)
}

fn default_query_packets_chunk_size() -> usize {
    50
}

fn default_clock_drift() -> Duration {
    Duration::from_secs(5)
}

fn default_event_poll_interval() -> Option<Duration> {
    Some(Duration::from_secs(5))
}

fn default_mithril_certification_timeout() -> Duration {
    Duration::from_secs(10 * 60)
}

fn default_mithril_poll_interval() -> Duration {
    Duration::from_secs(5)
}

fn default_mithril_wait_log_interval() -> Duration {
    Duration::from_secs(30)
}

impl Default for CardanoConfig {
    fn default() -> Self {
        Self {
            id: ChainId::from_string("cardano-test"),
            gateway_url: "http://localhost:3001".to_string(),
            network_id: 0,
            key_name: "default".to_string(),
            key_store_type: Store::Test,
            key_store_folder: None,
            account: 0,
            max_block_time: default_max_block_time(),
            packet_filter: PacketFilter::default(),
            trust_threshold: None,
            query_packets_chunk_size: default_query_packets_chunk_size(),
            clear_interval: None,
            clock_drift: default_clock_drift(),
            client_refresh_rate: default::client_refresh_rate(),
            event_poll_interval: default_event_poll_interval(),
            mithril_certification_timeout: default_mithril_certification_timeout(),
            mithril_poll_interval: default_mithril_poll_interval(),
            mithril_wait_log_interval: default_mithril_wait_log_interval(),
        }
    }
}
