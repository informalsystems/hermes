/// Temporal files before prost files are merged into cosmos/ibc-proto-rs

use std::prelude::v1::*;

/// https://github.com/Stride-Labs/stride/blob/main/proto/stride/interchainquery/v1/messages.proto
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgSubmitQueryResponse {
    #[prost(string, tag="1")]
    pub chain_id: String,
    #[prost(string, tag="2")]
    pub query_id: String,
    #[prost(bytes="vec", tag="3")]
    pub result: Vec<u8>,
    #[prost(message, optional, tag="4")]
    pub proof_ops: Option<ProofOps>,
    #[prost(int64, tag="5")]
    pub height: i64,
    #[prost(string, tag="6")]
    pub from_address: String,
}

/// https://github.com/tendermint/tendermint/blob/main/proto/tendermint/crypto/proof.proto
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ProofOp {
    #[prost(string, tag="1")]
    pub r#type: String,
    #[prost(bytes="vec", tag="2")]
    pub key: Vec<u8>,
    #[prost(bytes="vec", tag="3")]
    pub data: Vec<u8>,
}
/// ProofOps is Merkle proof defined by the list of ProofOps
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ProofOps {
    #[prost(message, repeated, tag="1")]
    pub ops: Vec<ProofOp>,
}