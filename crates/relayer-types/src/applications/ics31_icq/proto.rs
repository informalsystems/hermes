/// Temporal files before prost files are merged into cosmos/ibc-proto-rs

use std::prelude::v1::*;
use tendermint_proto::crypto::ProofOps;

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