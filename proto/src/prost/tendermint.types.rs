#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ValidatorSet {
    #[prost(message, repeated, tag="1")]
    pub validators: ::std::vec::Vec<Validator>,
    #[prost(message, optional, tag="2")]
    pub proposer: ::std::option::Option<Validator>,
    #[prost(int64, tag="3")]
    pub total_voting_power: i64,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Validator {
    #[prost(bytes, tag="1")]
    pub address: std::vec::Vec<u8>,
    #[prost(message, optional, tag="2")]
    pub pub_key: ::std::option::Option<super::crypto::PublicKey>,
    #[prost(int64, tag="3")]
    pub voting_power: i64,
    #[prost(int64, tag="4")]
    pub proposer_priority: i64,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SimpleValidator {
    #[prost(message, optional, tag="1")]
    pub pub_key: ::std::option::Option<super::crypto::PublicKey>,
    #[prost(int64, tag="2")]
    pub voting_power: i64,
}
/// PartsetHeader
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PartSetHeader {
    #[prost(uint32, tag="1")]
    pub total: u32,
    #[prost(bytes, tag="2")]
    pub hash: std::vec::Vec<u8>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Part {
    #[prost(uint32, tag="1")]
    pub index: u32,
    #[prost(bytes, tag="2")]
    pub bytes: std::vec::Vec<u8>,
    #[prost(message, optional, tag="3")]
    pub proof: ::std::option::Option<super::crypto::Proof>,
}
/// BlockID
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BlockId {
    #[prost(bytes, tag="1")]
    pub hash: std::vec::Vec<u8>,
    #[prost(message, optional, tag="2")]
    pub part_set_header: ::std::option::Option<PartSetHeader>,
}
// --------------------------------

/// Header defines the structure of a Tendermint block header.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Header {
    /// basic block info
    #[prost(message, optional, tag="1")]
    pub version: ::std::option::Option<super::version::Consensus>,
    #[prost(string, tag="2")]
    pub chain_id: std::string::String,
    #[prost(int64, tag="3")]
    pub height: i64,
    #[prost(message, optional, tag="4")]
    pub time: ::std::option::Option<::prost_types::Timestamp>,
    /// prev block info
    #[prost(message, optional, tag="5")]
    pub last_block_id: ::std::option::Option<BlockId>,
    /// hashes of block data
    ///
    /// commit from validators from the last block
    #[prost(bytes, tag="6")]
    pub last_commit_hash: std::vec::Vec<u8>,
    /// transactions
    #[prost(bytes, tag="7")]
    pub data_hash: std::vec::Vec<u8>,
    /// hashes from the app output from the prev block
    ///
    /// validators for the current block
    #[prost(bytes, tag="8")]
    pub validators_hash: std::vec::Vec<u8>,
    /// validators for the next block
    #[prost(bytes, tag="9")]
    pub next_validators_hash: std::vec::Vec<u8>,
    /// consensus params for current block
    #[prost(bytes, tag="10")]
    pub consensus_hash: std::vec::Vec<u8>,
    /// state after txs from the previous block
    #[prost(bytes, tag="11")]
    pub app_hash: std::vec::Vec<u8>,
    /// root hash of all results from the txs from the previous block
    #[prost(bytes, tag="12")]
    pub last_results_hash: std::vec::Vec<u8>,
    /// consensus info
    ///
    /// evidence included in the block
    #[prost(bytes, tag="13")]
    pub evidence_hash: std::vec::Vec<u8>,
    /// original proposer of the block
    #[prost(bytes, tag="14")]
    pub proposer_address: std::vec::Vec<u8>,
}
/// Data contains the set of transactions included in the block
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Data {
    /// Txs that will be applied by state @ block.Height+1.
    /// NOTE: not all txs here are valid.  We're just agreeing on the order first.
    /// This means that block.AppHash does not include these txs.
    #[prost(bytes, repeated, tag="1")]
    pub txs: ::std::vec::Vec<std::vec::Vec<u8>>,
    /// Volatile
    #[prost(bytes, tag="2")]
    pub hash: std::vec::Vec<u8>,
}
/// Vote represents a prevote, precommit, or commit vote from validators for
/// consensus.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Vote {
    #[prost(enumeration="SignedMsgType", tag="1")]
    pub r#type: i32,
    #[prost(int64, tag="2")]
    pub height: i64,
    #[prost(int32, tag="3")]
    pub round: i32,
    /// zero if vote is nil.
    #[prost(message, optional, tag="4")]
    pub block_id: ::std::option::Option<BlockId>,
    #[prost(message, optional, tag="5")]
    pub timestamp: ::std::option::Option<::prost_types::Timestamp>,
    #[prost(bytes, tag="6")]
    pub validator_address: std::vec::Vec<u8>,
    #[prost(int32, tag="7")]
    pub validator_index: i32,
    #[prost(bytes, tag="8")]
    pub signature: std::vec::Vec<u8>,
}
/// Commit contains the evidence that a block was committed by a set of validators.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Commit {
    #[prost(int64, tag="1")]
    pub height: i64,
    #[prost(int32, tag="2")]
    pub round: i32,
    #[prost(message, optional, tag="3")]
    pub block_id: ::std::option::Option<BlockId>,
    #[prost(message, repeated, tag="4")]
    pub signatures: ::std::vec::Vec<CommitSig>,
    #[prost(bytes, tag="5")]
    pub hash: std::vec::Vec<u8>,
    #[prost(message, optional, tag="6")]
    pub bit_array: ::std::option::Option<super::libs::bits::BitArray>,
}
/// CommitSig is a part of the Vote included in a Commit.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CommitSig {
    #[prost(enumeration="BlockIdFlag", tag="1")]
    pub block_id_flag: i32,
    #[prost(bytes, tag="2")]
    pub validator_address: std::vec::Vec<u8>,
    #[prost(message, optional, tag="3")]
    pub timestamp: ::std::option::Option<::prost_types::Timestamp>,
    #[prost(bytes, tag="4")]
    pub signature: std::vec::Vec<u8>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Proposal {
    #[prost(enumeration="SignedMsgType", tag="1")]
    pub r#type: i32,
    #[prost(int64, tag="2")]
    pub height: i64,
    #[prost(int32, tag="3")]
    pub round: i32,
    #[prost(int32, tag="4")]
    pub pol_round: i32,
    #[prost(message, optional, tag="5")]
    pub block_id: ::std::option::Option<BlockId>,
    #[prost(message, optional, tag="6")]
    pub timestamp: ::std::option::Option<::prost_types::Timestamp>,
    #[prost(bytes, tag="7")]
    pub signature: std::vec::Vec<u8>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignedHeader {
    #[prost(message, optional, tag="1")]
    pub header: ::std::option::Option<Header>,
    #[prost(message, optional, tag="2")]
    pub commit: ::std::option::Option<Commit>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LightBlock {
    #[prost(message, optional, tag="1")]
    pub signed_header: ::std::option::Option<SignedHeader>,
    #[prost(message, optional, tag="2")]
    pub validator_set: ::std::option::Option<ValidatorSet>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BlockMeta {
    #[prost(message, optional, tag="1")]
    pub block_id: ::std::option::Option<BlockId>,
    #[prost(int64, tag="2")]
    pub block_size: i64,
    #[prost(message, optional, tag="3")]
    pub header: ::std::option::Option<Header>,
    #[prost(int64, tag="4")]
    pub num_txs: i64,
}
/// TxProof represents a Merkle proof of the presence of a transaction in the Merkle tree.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TxProof {
    #[prost(bytes, tag="1")]
    pub root_hash: std::vec::Vec<u8>,
    #[prost(bytes, tag="2")]
    pub data: std::vec::Vec<u8>,
    #[prost(message, optional, tag="3")]
    pub proof: ::std::option::Option<super::crypto::Proof>,
}
/// BlockIdFlag indicates which BlcokID the signature is for
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum BlockIdFlag {
    Unknown = 0,
    Absent = 1,
    Commit = 2,
    Nil = 3,
}
/// SignedMsgType is a type of signed message in the consensus.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum SignedMsgType {
    Unknown = 0,
    /// Votes
    Prevote = 1,
    Precommit = 2,
    /// Proposals
    Proposal = 32,
}
