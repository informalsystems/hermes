use prost_amino_derive::Message;
use tendermint::amino_types::TimeMsg;

#[derive(Clone, PartialEq, Message)]
// TODO: remove when the sdk switches to vanilla proto
#[amino_name = "ibc/client/tendermint/ClientState"]
struct ClientState {
    #[prost_amino(string, tag = "1")]
    pub id: String,

    #[prost_amino(int64, tag = "2")]
    pub trusting_period: i64,

    #[prost_amino(int64, tag = "3")]
    pub unbonding_period: i64,

    #[prost_amino(uint64, tag = "4")]
    pub frozen_height: crate::Height,

    // TODO: remove `amino_name` annotation as soon as this is actually protobuf
    #[prost_amino(message, tag = "5", amino_name = "ibc/client/tendermint/Header")]
    pub latest_header: Option<Header>,
}
// ---------------------------------------------------------------------
// TODO: these types below should actually live in tendermint-rs!
// under tendermint/src/amino_types/
// these should be re-used here
// see: https://github.com/informalsystems/tendermint-rs/issues/203
// ---------------------------------------------------------------------

#[derive(Clone, PartialEq, Message)]
pub struct Header {
    #[prost_amino(message, tag = "1")]
    pub signed_header: Option<SignedHeader>,
    // pub validator_set: ValidatorSet,
    // pub next_validator_set: ValidatorSet,
}

#[derive(Clone, PartialEq, Message)]
pub struct SignedHeader {
    /// Block header
    #[prost_amino(message, tag = "1")]
    pub header: Option<BlockHeader>,
    /// Commit containing signatures for the header
    #[prost_amino(message, tag = "2")]
    pub commit: Option<BlockCommit>,
}

// v0.33:
// https://github.com/tendermint/tendermint/blob/2544a5cf3a2b2e5dd90c6b15c23bcb82b9b23a31/types/block.go#L318-L348
#[derive(Clone, PartialEq, Message)]
pub struct BlockHeader {
    // TODO: figure out what amino used here actually (`repeated` or `optional`=:
    // https://github.com/danburkert/prost#field-modifiers
    // basic block info:
    #[prost_amino(message, tag = "1")]
    pub version: Option<Version>,
    #[prost_amino(string, tag = "2")]
    pub chain_id: String,
    #[prost_amino(int64, tag = "3")]
    pub height: i64,
    #[prost_amino(message, tag = "4")]
    pub time: Option<TimeMsg>,

    // Previous block info
    /// Previous block info
    #[prost_amino(message, tag = "5")]
    pub last_block_id: Option<BlockId>,
    // hashes of block data
    /// Commit from validators from the last block
    #[prost_amino(bytes, tag = "6")]
    pub last_commit_hash: Vec<u8>,
    /// Merkle root of transaction hashes
    #[prost_amino(bytes, tag = "7")]
    pub data_hash: Vec<u8>,

    // hashes from the app output from the prev block
    /// Validators for the current block
    #[prost_amino(bytes, tag = "8")]
    pub validators_hash: Vec<u8>,
    /// Validators for the next block
    #[prost_amino(bytes, tag = "9")]
    pub next_validators_hash: Vec<u8>,
    /// Consensus params for the current block
    #[prost_amino(bytes, tag = "10")]
    pub consensus_hash: Vec<u8>,
    /// State after txs from the previous block
    #[prost_amino(bytes, tag = "11")]
    pub app_hash: Vec<u8>,
    // root hash of all results from the txs from the previous block
    /// Root hash of all results from the txs from the previous block
    #[prost_amino(bytes, tag = "12")]
    pub last_results_hash: Vec<u8>,

    // consensus info
    /// Hash of evidence included in the block
    #[prost_amino(bytes, tag = "13")]
    pub evidence_hash: Vec<u8>,
    /// Original proposer of the block
    #[prost_amino(bytes, tag = "14")]
    pub proposer_address: Vec<u8>,
}

#[derive(Clone, PartialEq, Message)]
pub struct BlockCommit {
    // TODO
}

#[derive(Clone, PartialEq, Message)]
pub struct BlockId {
    #[prost_amino(bytes, tag = "1")]
    pub hash: Vec<u8>,
    #[prost_amino(message, tag = "14")]
    pub parts: Option<PartSetHeader>,
}

#[derive(Clone, PartialEq, Message)]
pub struct PartSetHeader {
    #[prost_amino(int64, tag = "1")]
    pub total: i64,
    #[prost_amino(bytes, tag = "2")]
    pub hash: Vec<u8>,
}

#[derive(Clone, PartialEq, Message)]
pub struct Version {
    /// Block version
    #[prost_amino(uint64, tag = "1")]
    pub block: u64,
    /// App version
    #[prost_amino(uint64, tag = "2")]
    pub app: u64,
}

#[cfg(test)]
mod tests {}
