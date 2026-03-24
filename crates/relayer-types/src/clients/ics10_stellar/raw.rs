//! Raw protobuf types for the Stellar IBC light client (`10-stellar`).
//!
//! These types mirror what would be generated from the following proto package:
//!
//! ```protobuf
//! package ibc.lightclients.stellar.v1;
//! ```

use ibc_proto::ibc::core::client::v1::Height as RawHeight;
use prost::Message;

// ---------------------------------------------------------------------------
// Type URLs
// ---------------------------------------------------------------------------

pub const STELLAR_HEADER_TYPE_URL: &str = "/ibc.lightclients.stellar.v1.Header";
pub const STELLAR_CLIENT_STATE_TYPE_URL: &str = "/ibc.lightclients.stellar.v1.ClientState";
pub const STELLAR_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.lightclients.stellar.v1.ConsensusState";
pub const STELLAR_MISBEHAVIOUR_TYPE_URL: &str = "/ibc.lightclients.stellar.v1.Misbehaviour";

// ---------------------------------------------------------------------------
// Header
// ---------------------------------------------------------------------------

/// Protobuf encoding of a Stellar light client header.
///
/// Equivalent proto definition:
/// ```protobuf
/// message Header {
///   ibc.core.client.v1.Height height       = 1;
///   bytes                     ledger_hash  = 2; // SHA-256 of LedgerHeader XDR, 32 bytes
///   uint64                    timestamp_ns = 3; // ledger close time, Unix nanoseconds
///   uint32                    ledger_seq   = 4; // Stellar ledger sequence number
///   bytes                     scp_envelopes = 5; // XDR-encoded SCPEnvelope[] (EXTERNALIZE)
/// }
/// ```
#[derive(Clone, PartialEq, Message)]
pub struct RawHeader {
    /// IBC consensus height (revision_number=0, revision_height=ledger_seq)
    #[prost(message, optional, tag = "1")]
    pub height: Option<RawHeight>,
    /// SHA-256 hash of the LedgerHeader XDR (32 bytes)
    #[prost(bytes = "vec", tag = "2")]
    pub ledger_hash: Vec<u8>,
    /// Ledger close time as Unix nanoseconds
    #[prost(uint64, tag = "3")]
    pub timestamp_ns: u64,
    /// Stellar ledger sequence number (block height)
    #[prost(uint32, tag = "4")]
    pub ledger_seq: u32,
    /// XDR-encoded SCP EXTERNALIZE envelopes proving consensus for this ledger
    #[prost(bytes = "vec", tag = "5")]
    pub scp_envelopes: Vec<u8>,
}

// ---------------------------------------------------------------------------
// ClientState
// ---------------------------------------------------------------------------

/// Protobuf encoding of the Stellar light client state.
///
/// Equivalent proto definition:
/// ```protobuf
/// message ClientState {
///   string                    chain_id          = 1;
///   ibc.core.client.v1.Height latest_height     = 2;
///   uint64                    trusting_period_ns = 3; // nanoseconds
///   uint64                    unbonding_period_ns = 4; // nanoseconds
///   ibc.core.client.v1.Height frozen_height     = 5; // zero if not frozen
/// }
/// ```
#[derive(Clone, PartialEq, Message)]
pub struct RawClientState {
    /// Chain identifier of the Stellar network being tracked
    #[prost(string, tag = "1")]
    pub chain_id: String,
    /// Height of the most recent trusted ledger
    #[prost(message, optional, tag = "2")]
    pub latest_height: Option<RawHeight>,
    /// Duration the client trusts headers for, in nanoseconds
    #[prost(uint64, tag = "3")]
    pub trusting_period_ns: u64,
    /// Unbonding period of the chain, in nanoseconds
    #[prost(uint64, tag = "4")]
    pub unbonding_period_ns: u64,
    /// Height at which the client was frozen due to misbehaviour; zero if active
    #[prost(message, optional, tag = "5")]
    pub frozen_height: Option<RawHeight>,
}

// ---------------------------------------------------------------------------
// ConsensusState
// ---------------------------------------------------------------------------

/// Protobuf encoding of a Stellar consensus state.
///
/// Equivalent proto definition:
/// ```protobuf
/// message ConsensusState {
///   bytes  root         = 1; // bucketListHash from LedgerHeader, 32 bytes
///   uint64 timestamp_ns = 2; // ledger close time, Unix nanoseconds
///   uint32 ledger_seq   = 3; // Stellar ledger sequence number
/// }
/// ```
#[derive(Clone, PartialEq, Message)]
pub struct RawConsensusState {
    /// Commitment root: the `bucketListHash` from the Stellar LedgerHeader (32 bytes).
    /// This commits to the full on-chain state at this ledger.
    #[prost(bytes = "vec", tag = "1")]
    pub root: Vec<u8>,
    /// Ledger close time as Unix nanoseconds
    #[prost(uint64, tag = "2")]
    pub timestamp_ns: u64,
    /// Stellar ledger sequence number
    #[prost(uint32, tag = "3")]
    pub ledger_seq: u32,
}

// ---------------------------------------------------------------------------
// Misbehaviour
// ---------------------------------------------------------------------------

/// Protobuf encoding of Stellar light client misbehaviour (two conflicting headers).
///
/// Equivalent proto definition:
/// ```protobuf
/// message Misbehaviour {
///   string client_id = 1;
///   Header header_1  = 2;
///   Header header_2  = 3;
/// }
/// ```
#[derive(Clone, PartialEq, Message)]
pub struct RawMisbehaviour {
    /// IBC client identifier on the host chain
    #[prost(string, tag = "1")]
    pub client_id: String,
    /// First conflicting header
    #[prost(message, optional, tag = "2")]
    pub header_1: Option<RawHeader>,
    /// Second conflicting header at the same height
    #[prost(message, optional, tag = "3")]
    pub header_2: Option<RawHeader>,
}
