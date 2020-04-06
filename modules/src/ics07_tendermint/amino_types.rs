use prost_amino_derive::{Enumeration, Message};
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

    #[prost_amino(int64, tag = "4")]
    pub frozen_height: i64,

    // TODO: remove `amino_name` annotation as soon as this is actually protobuf
    #[prost_amino(message, amino_name = "ibc/client/tendermint/Header")]
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
    #[prost_amino(message)]
    pub validator_set: Option<ValidatorSet>,
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

#[derive(Clone, PartialEq, Message)]
pub struct ValidatorSet {
    #[prost_amino(message, repeated, tag = "1")]
    validators: Vec<Validator>,
}
#[derive(Clone, PartialEq, Message)]
pub struct Validator {
    #[prost_amino(bytes, tag = "1")]
    address: Vec<u8>,
    #[prost_amino(bytes, tag = "2")]
    pub_key: Vec<u8>,
    #[prost_amino(int64, tag = "3")]
    voting_power: i64,

    #[prost_amino(int64, tag = "4")]
    proposer_priority: i64,
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
    #[prost_amino(int64, tag = "1")]
    pub height: i64,
    #[prost_amino(int64, tag = "2")]
    pub round: i64,
    #[prost_amino(message, tag = "3")]
    pub block_id: Option<BlockId>,
    #[prost_amino(message, repeated, tag = "4")]
    pub signatures: Vec<CommitSig>,
}

#[derive(Clone, PartialEq, Message)]
pub struct CommitSig {
    #[prost_amino(enumeration = "BlockIDFlag", tag = "1")]
    block_id_flag: i32,
    #[prost_amino(bytes, tag = "2")]
    validator_address: Vec<u8>,
    #[prost_amino(message, tag = "3")]
    time_stamp: Option<TimeMsg>,
    #[prost_amino(bytes, tag = "4")]
    signature: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Enumeration)]
pub enum BlockIDFlag {
    /// BlockIDFlagAbsent - no vote was received from a validator.
    BlockIDFlagAbsent = 1,
    /// BlockIDFlagCommit - voted for the Commit.BlockID.
    BlockIDFlagCommit = 2,
    /// BlockIDFlagNil - voted for nil.
    BlockIDFlagNil = 3,
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
mod tests {
    use crate::ics07_tendermint::amino_types::ClientState;
    use prost_amino::Message;

    #[test]
    fn roundtrip_test_vector() {
        // payload dumped in test TestVerifyClientConsensusState from ibc-alpha branch
        // https://github.com/cosmos/cosmos-sdk/blob/df5badaf4c2bffde370d7cdee95ff9c1d15e7577/x/ibc/07-tendermint/types/client_state_test.go#L49
        // by dumping the `bz` of `bz, err := suite.cdc.MarshalBinaryLengthPrefixed(tc.clientState)`
        // Note: there is no reason for this to be length prefixed and this will likely change
        //
        // There are also decode_length_delimited() / encode_length_delimited but these are not
        // necessary as registered types are always length encoded
        let payload = vec![
            0x13, 0x21, 0xa1, 0x88, 0x96, 0xa, 0x4, 0x67, 0x61, 0x69, 0x61, 0x10, 0x80, 0x80, 0xc8, 0x92, 0xff, 0x83, 0x93, 0x2,

    ];
        let got_cs = ClientState::decode(payload.as_ref()).expect("could not decode");
        let mut got_back = vec![];
        got_cs.encode(&mut got_back).expect("encoding failed");
        assert_eq!(payload, got_back);
    }
}
