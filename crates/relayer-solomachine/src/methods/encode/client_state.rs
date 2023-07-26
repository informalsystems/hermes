#![allow(non_snake_case)]

use ibc_proto::google::protobuf::Any;
use ibc_relayer_cosmos::methods::encode::encode_to_any;
use prost::{EncodeError, Message};

use crate::methods::encode::consensus_state::{to_proto_consensus_state, ProtoConsensusState};
use crate::types::client_state::SolomachineClientState;

const TYPE_URL: &str = "/ibc.lightclients.solomachine.v3.ClientState";

#[derive(Message)]
pub struct ProtoClientState {
    #[prost(uint64, tag = "1")]
    pub sequence: u64,
    #[prost(bool, tag = "2")]
    pub is_frozen: bool,
    #[prost(message, optional, tag = "3")]
    pub consensus_state: Option<ProtoConsensusState>,
}

pub fn encode_client_state(client_state: &SolomachineClientState) -> Result<Any, EncodeError> {
    let proto_consensus_state = to_proto_consensus_state(&client_state.consensus_state);

    let proto_client_state = ProtoClientState {
        sequence: client_state.sequence,
        is_frozen: client_state.is_frozen,
        consensus_state: Some(proto_consensus_state),
    };

    encode_to_any(TYPE_URL, &proto_client_state)
}
