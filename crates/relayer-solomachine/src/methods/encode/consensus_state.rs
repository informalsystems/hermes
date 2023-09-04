#![allow(non_snake_case)]

use ibc_proto::google::protobuf::Any;
use ibc_relayer_cosmos::methods::encode::encode_to_any;
use prost::{EncodeError, Message};

use crate::types::consensus_state::SolomachineConsensusState;

use super::public_key::encode_public_key;

const TYPE_URL: &str = "/ibc.lightclients.solomachine.v3.ConsensusState";

#[derive(Message)]
pub struct ProtoConsensusState {
    #[prost(message, optional, tag = "1")]
    pub public_key: Option<Any>,
    #[prost(string, tag = "2")]
    pub diversifier: String,
    #[prost(uint64, tag = "3")]
    pub timestamp: u64,
}

pub fn to_proto_consensus_state(
    consensus_state: &SolomachineConsensusState,
) -> ProtoConsensusState {
    let proto_public_key = consensus_state
        .clone()
        .public_key
        .map(|key| encode_public_key(&key));

    ProtoConsensusState {
        public_key: proto_public_key,
        diversifier: consensus_state.diversifier.clone(),
        timestamp: consensus_state.timestamp,
    }
}

pub fn encode_consensus_state(
    consensus_state: &SolomachineConsensusState,
) -> Result<Any, EncodeError> {
    let proto_consensus_state = to_proto_consensus_state(consensus_state);
    encode_to_any(TYPE_URL, &proto_consensus_state)
}
