//! Defines the consensus state type for the ICS-08 Wasm light client.

use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use serde::{Deserialize, Serialize};

use ibc_proto::ibc::lightclients::wasm::v1::ConsensusState as RawConsensusState;

use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState as Ics02ConsensusState;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::timestamp::Timestamp;

use super::error::Error;

pub const WASM_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.lightclients.wasm.v1.ConsensusState";

/// The Wasm consensus state tracks the consensus state of the Wasm client.
/// Binary data represented by the data field is opaque and only interpreted by the Wasm contract
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusState {
    pub data: Vec<u8>,
}

impl Ics02ConsensusState for ConsensusState {
    fn client_type(&self) -> ClientType {
        ClientType::Wasm
    }

    fn root(&self) -> &CommitmentRoot {
        todo!()
    }

    fn timestamp(&self) -> Timestamp {
        todo!()
    }
}

impl Protobuf<RawConsensusState> for ConsensusState {}

impl From<ConsensusState> for RawConsensusState {
    fn from(value: ConsensusState) -> Self {
        RawConsensusState { data: value.data }
    }
}

impl TryFrom<RawConsensusState> for ConsensusState {
    type Error = Error;

    fn try_from(value: RawConsensusState) -> Result<Self, Self::Error> {
        Ok(Self { data: value.data })
    }
}

impl Protobuf<Any> for ConsensusState {}

impl From<ConsensusState> for Any {
    fn from(consensus_state: ConsensusState) -> Self {
        Any {
            type_url: WASM_CONSENSUS_STATE_TYPE_URL.to_string(),
            value: Protobuf::<RawConsensusState>::encode_vec(consensus_state),
        }
    }
}

impl TryFrom<Any> for ConsensusState {
    type Error = Ics02Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        use bytes::Buf;
        use core::ops::Deref;
        use prost::Message;

        fn decode_consensus_state<B: Buf>(buf: B) -> Result<ConsensusState, Error> {
            RawConsensusState::decode(buf)
                .map_err(Error::decode)?
                .try_into()
        }

        match raw.type_url.as_str() {
            WASM_CONSENSUS_STATE_TYPE_URL => {
                decode_consensus_state(raw.value.deref()).map_err(Into::into)
            }
            _ => Err(Ics02Error::unknown_consensus_state_type(raw.type_url)),
        }
    }
}
