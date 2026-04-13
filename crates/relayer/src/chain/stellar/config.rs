use core::time::Duration;
use std::path::PathBuf;

use serde_derive::{Deserialize, Serialize};

use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::config::{default, PacketFilter};
use crate::keyring::Store;

/// Configuration for a Stellar chain endpoint.
///
/// Stellar does not use gRPC — it exposes a JSON-RPC 2.0 HTTP interface via `stellar-rpc`.
/// IBC logic on Stellar is implemented as a Soroban smart contract.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct StellarConfig {
    /// Chain identifier (e.g. `stellar-local`, `stellar-testnet-1`)
    pub id: ChainId,

    /// stellar-rpc HTTP endpoint (e.g. `http://127.0.0.1:8000/rpc`)
    pub rpc_url: String,

    /// Network passphrase, required for transaction signing.
    /// - Standalone devnet: `"Standalone Network ; February 2017"`
    /// - Testnet: `"Test SDF Network ; September 2015"`
    /// - Mainnet: `"Public Global Stellar Network ; September 2015"`
    pub network_passphrase: String,

    /// C... StrKey address of the deployed IBC Soroban contract.
    pub ibc_contract_id: String,

    /// Name of the signing key in the Hermes keystore.
    pub key_name: String,

    /// Keystore backend (`Test` for development, `Os` for production).
    #[serde(default)]
    pub key_store_type: Store,

    /// Override for the keystore directory path.
    #[serde(default)]
    pub key_store_folder: Option<PathBuf>,

    /// Maximum expected time between ledger closes.
    /// Stellar closes ledgers approximately every 5 seconds.
    #[serde(default = "default_max_block_time", with = "humantime_serde")]
    pub max_block_time: Duration,

    /// Clock drift tolerance between local clock and chain timestamps.
    #[serde(default = "default_clock_drift", with = "humantime_serde")]
    pub clock_drift: Duration,

    /// How often to poll `getLatestLedger` for new blocks.
    /// Stellar has ~5s ledger close time; 3s is a reasonable poll interval.
    #[serde(default = "default_event_poll_interval", with = "humantime_serde")]
    pub event_poll_interval: Duration,

    /// Maximum number of packets to include in a single query.
    #[serde(default = "default::query_packets_chunk_size")]
    pub query_packets_chunk_size: usize,

    /// Optional interval (in blocks) for clearing unreceived packets.
    #[serde(default)]
    pub clear_interval: Option<u64>,

    /// Channel/port filter for packet relaying.
    #[serde(default)]
    pub packet_filter: PacketFilter,
}

fn default_max_block_time() -> Duration {
    Duration::from_secs(10)
}

fn default_clock_drift() -> Duration {
    Duration::from_secs(5)
}

fn default_event_poll_interval() -> Duration {
    Duration::from_secs(3)
}
