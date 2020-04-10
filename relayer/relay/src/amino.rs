use crate::tx;
use prost_amino_derive::Message;

use std::time::Duration;

use tendermint::{amino_types, block, validator};

#[derive(Clone, Message)]
pub struct Version {
    #[prost_amino(uint64, tag = "1")]
    pub block: u64,
    #[prost_amino(uint64)]
    pub app: u64,
}

#[derive(Clone, Message)]
pub struct Header {
    #[prost_amino(message, tag = "1")]
    pub version: Option<Version>,
    #[prost_amino(string)]
    pub chain_id: String,
    #[prost_amino(int64)]
    pub height: i64,
    #[prost_amino(message)]
    pub time: Option<amino_types::time::TimeMsg>,
    #[prost_amino(message)]
    pub last_block_id: Option<amino_types::BlockId>,
    #[prost_amino(bytes)]
    pub last_commit_hash: Vec<u8>,
    #[prost_amino(bytes)]
    pub data_hash: Vec<u8>,
    #[prost_amino(bytes)]
    pub validators_hash: Vec<u8>,
    #[prost_amino(bytes)]
    pub next_validators_hash: Vec<u8>,
    #[prost_amino(bytes)]
    pub consensus_hash: Vec<u8>,
    #[prost_amino(bytes)]
    pub app_hash: Vec<u8>,
    #[prost_amino(bytes)]
    pub last_results_hash: Vec<u8>,
    #[prost_amino(bytes)]
    pub evidence_hash: Vec<u8>,
    #[prost_amino(bytes)]
    pub proposer_address: Vec<u8>,
}

impl From<&block::Header> for Header {
    fn from(header: &block::Header) -> Header {
        Header {
            version: Some(Version {
                block: header.version.block,
                app: header.version.app,
            }),
            chain_id: header.chain_id.as_str().to_string(),
            height: i64::from(header.height),
            time: Some(amino_types::time::TimeMsg::from(header.time)),
            last_block_id: match &header.last_block_id {
                Some(id) => Some(amino_types::block_id::BlockId::from(id)),
                None => None,
            },
            last_commit_hash: option_hash(header.last_commit_hash),
            data_hash: option_hash(header.data_hash),
            validators_hash: hash(header.validators_hash),
            next_validators_hash: hash(header.next_validators_hash),
            consensus_hash: hash(header.consensus_hash),
            app_hash: header.app_hash.clone(), // XXX
            last_results_hash: option_hash(header.last_results_hash),
            evidence_hash: option_hash(header.evidence_hash),
            proposer_address: header.proposer_address.as_bytes().to_vec(),
        }
    }
}

fn option_hash(oh: Option<tendermint::Hash>) -> Vec<u8> {
    match oh {
        Some(h) => hash(h),
        None => Vec::new(),
    }
}

fn hash(h: tendermint::Hash) -> Vec<u8> {
    h.as_bytes().to_vec()
}

#[derive(Clone, Message)]
pub struct CommitSig {
    #[prost_amino(uint32, tag = "1")]
    block_id_flag: u32,
    #[prost_amino(bytes)]
    validator_address: Vec<u8>,
    #[prost_amino(message)]
    timestamp: Option<amino_types::time::TimeMsg>,
    #[prost_amino(bytes)]
    signature: Vec<u8>,
}

impl From<&block::CommitSig> for CommitSig {
    fn from(cs: &block::CommitSig) -> Self {
        CommitSig {
            block_id_flag: cs.block_id_flag.to_u32(),
            validator_address: match cs.validator_address {
                Some(addr) => addr.as_bytes().to_vec(),
                None => Vec::new(),
            },
            timestamp: Some(amino_types::time::TimeMsg::from(cs.timestamp)),
            signature: match &cs.signature {
                Some(sig) => sig.as_bytes().to_vec(),
                None => Vec::new(),
            },
        }
    }
}

#[derive(Clone, Message)]
pub struct Commit {
    #[prost_amino(int64, tag = "1")]
    height: i64,
    #[prost_amino(int64)]
    round: i64,
    #[prost_amino(message)]
    block_id: Option<amino_types::BlockId>,
    #[prost_amino(message, repeated)]
    signatures: Vec<CommitSig>,
}

impl From<&block::Commit> for Commit {
    fn from(commit: &block::Commit) -> Commit {
        let mut sigs = Vec::new();
        for sig in commit.signatures.iter() {
            sigs.push(CommitSig::from(sig))
        }
        Commit {
            height: i64::from(commit.height),
            round: commit.round as i64, // XXX
            block_id: Some(amino_types::block_id::BlockId::from(&commit.block_id)),
            signatures: sigs,
        }
    }
}

#[derive(Clone, Message)]
pub struct Validator {
    #[prost_amino(bytes, tag = "1")]
    address: Vec<u8>,
    #[prost_amino(bytes)]
    pub_key: Vec<u8>,
    #[prost_amino(int64)] 
    voting_power: i64,

    // XXX: the Go version also has ProposerPriority!
}

impl From<&validator::Info> for Validator{
    fn from(val: &validator::Info) -> Self {
        Validator{
            address: val.address.as_bytes().to_vec(),
            pub_key: val.pub_key.as_bytes(),
            voting_power: val.voting_power.value() as i64, // XXX
        }
    }
}


#[derive(Clone, Message)]
pub struct ValidatorSet {
    #[prost_amino(message, repeated, tag = "1")]
    validators: Vec<Validator>,

    // XXX: the Go version also has the proposer
}

impl From<&validator::Set> for ValidatorSet {
    fn from(valset: &validator::Set) -> Self {
        let mut vals = Vec::new();
        for val in valset.validators().iter(){
            vals.push(Validator::from(val));
        }
        ValidatorSet{
            validators: vals,
        }
    }

}



#[derive(Clone, Message)]
pub struct SignedHeader {
    #[prost_amino(message, tag = "1")]
    header: Option<Header>,
    #[prost_amino(message)]
    commit: Option<Commit>,
}

#[derive(Clone, Message)]
pub struct SignedHeaderVals {
    #[prost_amino(message, tag = "1")]
    SignedHeader: Option<SignedHeader>,
    #[prost_amino(message)]
    validator_set: Option<ValidatorSet>,
}

#[derive(Clone, Message)]
pub struct MsgCreateClient {
    #[prost_amino(string, tag = "1")]
    client_id: String,
    #[prost_amino(message)]
    header: Option<SignedHeaderVals>,
    #[prost_amino(message)]
    trusting_period: Option<amino_types::time::TimeMsg>,
    #[prost_amino(message)]
    unbonding_period:  Option<amino_types::time::TimeMsg>,
    #[prost_amino(bytes)]
    address: Vec<u8>,
}

impl From<&tx::MsgCreateClientInner> for MsgCreateClient {
    fn from(msg: &tx::MsgCreateClientInner) -> Self {
        MsgCreateClient {
            client_id: msg.client_id.clone(),
            header: Some(SignedHeaderVals{
                SignedHeader: Some(SignedHeader{
                    header: Some(Header::from(&msg.header.SignedHeader.header)),
                    commit: Some(Commit::from(&msg.header.SignedHeader.commit)),
                }),
                validator_set: Some(ValidatorSet::from(&msg.header.validator_set)),
            }),
            trusting_period: Some(duration(msg.trusting_period)),
            unbonding_period: Some(duration(msg.unbonding_period)),
            address: msg.address.as_ref().to_vec(),
        }

    }
}

fn duration(d: Duration) -> amino_types::time::TimeMsg{
        let seconds = d.as_secs() as i64;
        let nanos = d.subsec_nanos() as i32;
        amino_types::time::TimeMsg { seconds, nanos }
}


