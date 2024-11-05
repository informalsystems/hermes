//! Defines the consensus state type for the ICS-08 Wasm light client.

use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};

use ibc_proto::ibc::lightclients::wasm::v1::ConsensusState as RawConsensusState;

use crate::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState as Ics02ConsensusState;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::timestamp::Timestamp;

use super::error::Error;

pub const WASM_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.lightclients.wasm.v1.ConsensusState";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WasmUnderlyingConsensusState {
    Tendermint(TmConsensusState),
}

impl Ics02ConsensusState for WasmUnderlyingConsensusState {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(tm_consensus_state) => tm_consensus_state.client_type(),
        }
    }

    fn root(&self) -> &CommitmentRoot {
        match self {
            Self::Tendermint(tm_consensus_state) => tm_consensus_state.root(),
        }
    }

    fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(tm_consensus_state) => tm_consensus_state.timestamp(),
        }
    }
}

/// The Wasm consensus state tracks the consensus state of the Wasm client.
/// Binary data represented by the data field is opaque and only interpreted by the Wasm contract
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusState {
    pub underlying: WasmUnderlyingConsensusState,
}

impl ConsensusState {
    pub const TYPE_URL: &'static str = WASM_CONSENSUS_STATE_TYPE_URL;
}

impl Ics02ConsensusState for ConsensusState {
    fn client_type(&self) -> ClientType {
        ClientType::Wasm
    }

    fn root(&self) -> &CommitmentRoot {
        self.underlying.root()
    }

    fn timestamp(&self) -> Timestamp {
        self.underlying.timestamp()
    }
}

fn encode_underlying_consensus_state(consensus_state: WasmUnderlyingConsensusState) -> Vec<u8> {
    match consensus_state {
        WasmUnderlyingConsensusState::Tendermint(tm_state) => Any::from(tm_state).encode_to_vec(),
    }
}

fn decode_underlying_consensus_state(data: &[u8]) -> Result<WasmUnderlyingConsensusState, Error> {
    let any = Any::decode(data)?;

    match any.type_url.as_str() {
        TmConsensusState::TYPE_URL => Ok(WasmUnderlyingConsensusState::Tendermint(
            TmConsensusState::try_from(any)?,
        )),
        _ => Err(Error::unsupported_wasm_consensus_state_type(any.type_url)),
    }
}

impl Protobuf<RawConsensusState> for ConsensusState {}

impl From<ConsensusState> for RawConsensusState {
    fn from(consensus_state: ConsensusState) -> Self {
        RawConsensusState {
            data: encode_underlying_consensus_state(consensus_state.underlying),
        }
    }
}

impl TryFrom<RawConsensusState> for ConsensusState {
    type Error = Error;

    fn try_from(raw: RawConsensusState) -> Result<Self, Self::Error> {
        Ok(Self {
            underlying: decode_underlying_consensus_state(&raw.data)?,
        })
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

        fn decode_consensus_state<B: Buf>(buf: B) -> Result<ConsensusState, Error> {
            RawConsensusState::decode(buf)?.try_into()
        }

        match raw.type_url.as_str() {
            WASM_CONSENSUS_STATE_TYPE_URL => {
                decode_consensus_state(raw.value.deref()).map_err(Into::into)
            }
            _ => Err(Ics02Error::unknown_consensus_state_type(raw.type_url)),
        }
    }
}
