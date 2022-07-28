use crate::prelude::*;

use core::any::Any as CoreAny;
use core::marker::{Send, Sync};

use ibc_proto::google::protobuf::Any as ProtoAny;
use ibc_proto::ibc::core::client::v1::ConsensusStateWithHeight;
use serde::Serialize;
use tendermint_proto::Protobuf;

use crate::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::height::Height;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::timestamp::Timestamp;

#[cfg(any(test, feature = "mocks"))]
use crate::mock::client_state::MockConsensusState;

pub const TENDERMINT_CONSENSUS_STATE_TYPE_URL: &str =
    "/ibc.lightclients.tendermint.v1.ConsensusState";

pub const MOCK_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.mock.ConsensusState";

pub trait ConsensusState: core::fmt::Debug + Send + Sync + AsAny {
    /// Type of client associated with this consensus state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Commitment root of the consensus state, which is used for key-value pair verification.
    fn root(&self) -> &CommitmentRoot;

    fn encode_vec(&self) -> Result<Vec<u8>, Error>;
}

pub trait AsAny: CoreAny {
    fn as_any(&self) -> &dyn CoreAny;
}

impl<M: CoreAny + ConsensusState> AsAny for M {
    fn as_any(&self) -> &dyn CoreAny {
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "type")]
pub enum AnyConsensusState {
    Tendermint(TmConsensusState),

    #[cfg(any(test, feature = "mocks"))]
    Mock(MockConsensusState),
}

impl AnyConsensusState {
    pub fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(cs_state) => cs_state.timestamp.into(),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(mock_state) => mock_state.timestamp(),
        }
    }

    pub fn client_type(&self) -> ClientType {
        match self {
            AnyConsensusState::Tendermint(_cs) => ClientType::Tendermint,

            #[cfg(any(test, feature = "mocks"))]
            AnyConsensusState::Mock(_cs) => ClientType::Mock,
        }
    }

    pub fn boxed_dyn(self) -> Box<dyn ConsensusState> {
        match self {
            AnyConsensusState::Tendermint(cs) => Box::new(cs),

            #[cfg(any(test, feature = "mocks"))]
            AnyConsensusState::Mock(cs) => Box::new(cs),
        }
    }
}

impl Protobuf<ProtoAny> for AnyConsensusState {}

impl TryFrom<ProtoAny> for AnyConsensusState {
    type Error = Error;

    fn try_from(value: ProtoAny) -> Result<Self, Self::Error> {
        match value.type_url.as_str() {
            "" => Err(Error::empty_consensus_state_response()),

            TENDERMINT_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Tendermint(
                TmConsensusState::decode_vec(&value.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            #[cfg(any(test, feature = "mocks"))]
            MOCK_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Mock(
                MockConsensusState::decode_vec(&value.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            _ => Err(Error::unknown_consensus_state_type(value.type_url)),
        }
    }
}

impl From<AnyConsensusState> for ProtoAny {
    fn from(value: AnyConsensusState) -> Self {
        match value {
            AnyConsensusState::Tendermint(value) => ProtoAny {
                type_url: TENDERMINT_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: ConsensusState::encode_vec(&value)
                    .expect("encoding to `Any` from `AnyConsensusState::Tendermint`"),
            },
            #[cfg(any(test, feature = "mocks"))]
            AnyConsensusState::Mock(value) => ProtoAny {
                type_url: MOCK_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: ConsensusState::encode_vec(&value)
                    .expect("encoding to `Any` from `AnyConsensusState::Mock`"),
            },
        }
    }
}

#[cfg(any(test, feature = "mocks"))]
impl From<MockConsensusState> for AnyConsensusState {
    fn from(cs: MockConsensusState) -> Self {
        Self::Mock(cs)
    }
}

impl From<TmConsensusState> for AnyConsensusState {
    fn from(cs: TmConsensusState) -> Self {
        Self::Tendermint(cs)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AnyConsensusStateWithHeight {
    pub height: Height,
    pub consensus_state: AnyConsensusState,
}

impl Protobuf<ConsensusStateWithHeight> for AnyConsensusStateWithHeight {}

impl TryFrom<ConsensusStateWithHeight> for AnyConsensusStateWithHeight {
    type Error = Error;

    fn try_from(value: ConsensusStateWithHeight) -> Result<Self, Self::Error> {
        let state = value
            .consensus_state
            .map(AnyConsensusState::try_from)
            .transpose()?
            .ok_or_else(Error::empty_consensus_state_response)?;

        Ok(AnyConsensusStateWithHeight {
            height: value
                .height
                .and_then(|raw_height| raw_height.try_into().ok())
                .ok_or_else(Error::missing_height)?,
            consensus_state: state,
        })
    }
}

impl From<AnyConsensusStateWithHeight> for ConsensusStateWithHeight {
    fn from(value: AnyConsensusStateWithHeight) -> Self {
        ConsensusStateWithHeight {
            height: Some(value.height.into()),
            consensus_state: Some(value.consensus_state.into()),
        }
    }
}

impl ConsensusState for AnyConsensusState {
    fn client_type(&self) -> ClientType {
        self.client_type()
    }

    fn root(&self) -> &CommitmentRoot {
        match self {
            Self::Tendermint(cs_state) => cs_state.root(),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(mock_state) => mock_state.root(),
        }
    }

    fn encode_vec(&self) -> Result<Vec<u8>, Error> {
        Protobuf::encode_vec(self).map_err(Error::invalid_any_consensus_state)
    }
}
