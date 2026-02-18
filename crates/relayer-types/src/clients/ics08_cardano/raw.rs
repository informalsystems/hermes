//! Raw protobuf types for `ibc.lightclients.mithril.v1`.
//!
//! These message definitions mirror `cosmos/sidechain/proto/ibc/lightclients/mithril/v1/mithril.proto`.
//! They are intentionally kept local to `ibc-relayer-types` to enable encoding/decoding from
//! `google.protobuf.Any` without requiring upstream `ibc-proto` support.

use serde_derive::{Deserialize, Serialize};

#[derive(Clone, PartialEq, ::prost::Message, Serialize, Deserialize)]
pub struct Height {
    #[prost(uint64, tag = "1")]
    pub revision_number: u64,
    #[prost(uint64, tag = "2")]
    pub revision_height: u64,
}

#[derive(Clone, PartialEq, ::prost::Message, Serialize, Deserialize)]
pub struct ClientState {
    #[prost(string, tag = "1")]
    pub chain_id: ::prost::alloc::string::String,
    #[prost(message, optional, tag = "2")]
    pub latest_height: ::core::option::Option<Height>,
    #[prost(message, optional, tag = "3")]
    pub frozen_height: ::core::option::Option<Height>,
    #[prost(uint64, tag = "4")]
    pub current_epoch: u64,
    #[prost(message, optional, tag = "5")]
    pub trusting_period: ::core::option::Option<ibc_proto::google::protobuf::Duration>,
    #[prost(message, optional, tag = "6")]
    pub protocol_parameters: ::core::option::Option<MithrilProtocolParameters>,
    #[prost(string, repeated, tag = "7")]
    pub upgrade_path: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
    #[prost(bytes = "vec", tag = "8")]
    pub host_state_nft_policy_id: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "9")]
    pub host_state_nft_token_name: ::prost::alloc::vec::Vec<u8>,
}

#[derive(Clone, PartialEq, ::prost::Message, Serialize, Deserialize)]
pub struct ConsensusState {
    #[prost(uint64, tag = "1")]
    pub timestamp: u64,
    #[prost(message, optional, tag = "2")]
    pub first_cert_hash_latest_epoch: ::core::option::Option<MithrilCertificate>,
    #[prost(string, tag = "3")]
    pub latest_cert_hash_tx_snapshot: ::prost::alloc::string::String,
    #[prost(bytes = "vec", tag = "4")]
    pub ibc_state_root: ::prost::alloc::vec::Vec<u8>,
}

#[derive(Clone, PartialEq, ::prost::Message, Serialize, Deserialize)]
pub struct Misbehaviour {
    #[prost(string, tag = "1")]
    pub client_id: ::prost::alloc::string::String,
    #[prost(message, optional, tag = "2")]
    pub mithril_header_1: ::core::option::Option<MithrilHeader>,
    #[prost(message, optional, tag = "3")]
    pub mithril_header_2: ::core::option::Option<MithrilHeader>,
}

#[derive(Clone, PartialEq, ::prost::Message, Serialize, Deserialize)]
pub struct MithrilHeader {
    #[prost(message, optional, tag = "1")]
    pub mithril_stake_distribution: ::core::option::Option<MithrilStakeDistribution>,
    #[prost(message, optional, tag = "2")]
    pub mithril_stake_distribution_certificate: ::core::option::Option<MithrilCertificate>,
    #[prost(message, optional, tag = "3")]
    pub transaction_snapshot: ::core::option::Option<CardanoTransactionSnapshot>,
    #[prost(message, optional, tag = "4")]
    pub transaction_snapshot_certificate: ::core::option::Option<MithrilCertificate>,
    #[prost(message, repeated, tag = "9")]
    pub previous_mithril_stake_distribution_certificates:
        ::prost::alloc::vec::Vec<MithrilCertificate>,
    #[prost(string, tag = "5")]
    pub host_state_tx_hash: ::prost::alloc::string::String,
    #[prost(bytes = "vec", tag = "6")]
    pub host_state_tx_body_cbor: ::prost::alloc::vec::Vec<u8>,
    #[prost(uint32, tag = "7")]
    pub host_state_tx_output_index: u32,
    #[prost(bytes = "vec", tag = "8")]
    pub host_state_tx_proof: ::prost::alloc::vec::Vec<u8>,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct MithrilStakeDistribution {
    #[prost(uint64, tag = "1")]
    pub epoch: u64,
    #[prost(message, repeated, tag = "2")]
    pub signers_with_stake: ::prost::alloc::vec::Vec<SignerWithStake>,
    #[prost(string, tag = "3")]
    pub hash: ::prost::alloc::string::String,
    #[prost(string, tag = "4")]
    pub certificate_hash: ::prost::alloc::string::String,
    #[prost(uint64, tag = "5")]
    pub created_at: u64,
    #[prost(message, optional, tag = "6")]
    pub protocol_parameter: ::core::option::Option<MithrilProtocolParameters>,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct CardanoTransactionSnapshot {
    #[prost(string, tag = "1")]
    pub merkle_root: ::prost::alloc::string::String,
    #[prost(uint64, tag = "2")]
    pub epoch: u64,
    #[prost(uint64, tag = "3")]
    pub block_number: u64,
    #[prost(string, tag = "4")]
    pub hash: ::prost::alloc::string::String,
    #[prost(string, tag = "5")]
    pub certificate_hash: ::prost::alloc::string::String,
    #[prost(string, tag = "6")]
    pub created_at: ::prost::alloc::string::String,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct MithrilCertificate {
    #[prost(string, tag = "1")]
    pub hash: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub previous_hash: ::prost::alloc::string::String,
    #[prost(uint64, tag = "3")]
    pub epoch: u64,
    #[prost(message, optional, tag = "4")]
    pub signed_entity_type: ::core::option::Option<SignedEntityType>,
    #[prost(message, optional, tag = "5")]
    pub metadata: ::core::option::Option<CertificateMetadata>,
    #[prost(message, optional, tag = "6")]
    pub protocol_message: ::core::option::Option<ProtocolMessage>,
    #[prost(string, tag = "7")]
    pub signed_message: ::prost::alloc::string::String,
    #[prost(string, tag = "8")]
    pub aggregate_verification_key: ::prost::alloc::string::String,
    #[prost(string, tag = "9")]
    pub multi_signature: ::prost::alloc::string::String,
    #[prost(string, tag = "10")]
    pub genesis_signature: ::prost::alloc::string::String,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct CertificateMetadata {
    #[prost(string, tag = "1")]
    pub network: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub protocol_version: ::prost::alloc::string::String,
    #[prost(message, optional, tag = "3")]
    pub protocol_parameters: ::core::option::Option<MithrilProtocolParameters>,
    #[prost(string, tag = "4")]
    pub initiated_at: ::prost::alloc::string::String,
    #[prost(string, tag = "5")]
    pub sealed_at: ::prost::alloc::string::String,
    #[prost(message, repeated, tag = "6")]
    pub signers: ::prost::alloc::vec::Vec<SignerWithStake>,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct SignerWithStake {
    #[prost(string, tag = "1")]
    pub party_id: ::prost::alloc::string::String,
    #[prost(uint64, tag = "2")]
    pub stake: u64,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct ProtocolMessage {
    #[prost(message, repeated, tag = "1")]
    pub message_parts: ::prost::alloc::vec::Vec<MessagePart>,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct MessagePart {
    #[prost(enumeration = "ProtocolMessagePartKey", tag = "1")]
    pub protocol_message_part_key: i32,
    #[prost(string, tag = "2")]
    pub protocol_message_part_value: ::prost::alloc::string::String,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct MithrilProtocolParameters {
    #[prost(uint64, tag = "1")]
    pub k: u64,
    #[prost(uint64, tag = "2")]
    pub m: u64,
    #[prost(message, optional, tag = "3")]
    pub phi_f: ::core::option::Option<Fraction>,
}

#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    ::prost::Enumeration,
    Serialize,
    Deserialize,
)]
#[repr(i32)]
pub enum ProtocolMessagePartKey {
    Unspecified = 0,
    SnapshotDigest = 1,
    CardanoTransactionsMerkleRoot = 2,
    NextAggregateVerificationKey = 3,
    LatestImmutableFileNumber = 4,
    LatestBlockNumber = 5,
}

#[derive(Clone, PartialEq, ::prost::Message, Serialize, Deserialize)]
pub struct ProtocolGenesisSignature {
    #[prost(bytes = "vec", tag = "1")]
    pub signature: ::prost::alloc::vec::Vec<u8>,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct SignedEntityType {
    #[prost(oneof = "signed_entity_type::Entity", tags = "1, 2, 3, 4")]
    pub entity: ::core::option::Option<signed_entity_type::Entity>,
}

pub mod signed_entity_type {
    use super::*;

    #[derive(Clone, PartialEq, Eq, ::prost::Oneof, Serialize, Deserialize)]
    pub enum Entity {
        #[prost(message, tag = "1")]
        MithrilStakeDistribution(MithrilStakeDistribution),
        #[prost(message, tag = "2")]
        CardanoStakeDistribution(CardanoStakeDistribution),
        #[prost(message, tag = "3")]
        CardanoImmutableFilesFull(CardanoImmutableFilesFull),
        #[prost(message, tag = "4")]
        CardanoTransactions(CardanoTransactions),
    }
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct CardanoStakeDistribution {
    #[prost(uint64, tag = "1")]
    pub epoch: u64,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct CardanoImmutableFilesFull {
    #[prost(message, optional, tag = "1")]
    pub beacon: ::core::option::Option<CardanoDbBeacon>,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct CardanoTransactions {
    #[prost(uint64, tag = "1")]
    pub epoch: u64,
    #[prost(uint64, tag = "2")]
    pub block_number: u64,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct CardanoDbBeacon {
    #[prost(string, tag = "1")]
    pub network: ::prost::alloc::string::String,
    #[prost(uint64, tag = "2")]
    pub epoch: u64,
    #[prost(uint64, tag = "3")]
    pub immutable_file_number: u64,
}

#[derive(Clone, PartialEq, Eq, ::prost::Message, Serialize, Deserialize)]
pub struct Fraction {
    #[prost(uint64, tag = "1")]
    pub numerator: u64,
    #[prost(uint64, tag = "2")]
    pub denominator: u64,
}
