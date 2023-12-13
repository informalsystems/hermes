use serde::{Deserialize, Serialize};

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::ConsensusStateWithHeight;
use ibc_proto::ibc::lightclients::solomachine::v3::ConsensusState as RawSmConsensusState;
use ibc_proto::ibc::lightclients::tendermint::v1::ConsensusState as RawConsensusState;
use ibc_proto::Protobuf;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::{
    ConsensusState as TmConsensusState, TENDERMINT_CONSENSUS_STATE_TYPE_URL,
};
use ibc_relayer_types::clients::ics12_near::consensus_state::ConsensusState as NearConsensusState;
use ibc_relayer_types::clients::ics12_near::consensus_state::NEAR_CONSENSUS_STATE_TYPE_URL;
use ibc_relayer_types::core::ics02_client::client_type::ClientType;
use ibc_relayer_types::core::ics02_client::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics02_client::error::Error;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentRoot;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;

use ibc_relayer_types::clients::ics06_solomachine::consensus_state::ConsensusState as SmConsensusState;
use ibc_relayer_types::clients::ics06_solomachine::consensus_state::SOLOMACHINE_CONSENSUS_STATE_TYPE_URL;
use ics12_proto::v1::ConsensusState as RawNearConsensusState;

#[cfg(test)]
use ibc_proto::ibc::mock::ConsensusState as RawMockConsensusState;
#[cfg(test)]
use ibc_relayer_types::mock::consensus_state::MockConsensusState;
#[cfg(test)]
use ibc_relayer_types::mock::consensus_state::MOCK_CONSENSUS_STATE_TYPE_URL;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
#[non_exhaustive]
pub enum AnyConsensusState {
    Tendermint(TmConsensusState),
    Solomachine(SmConsensusState),
    Near(Box<NearConsensusState>),

    #[cfg(test)]
    Mock(MockConsensusState),
}

impl AnyConsensusState {
    pub fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(cs_state) => cs_state.timestamp.into(),
            Self::Solomachine(cs_state) => cs_state.timestamp,
            Self::Near(cs_state) => cs_state.timestamp(),

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.timestamp(),
        }
    }

    pub fn client_type(&self) -> ClientType {
        match self {
            AnyConsensusState::Tendermint(_cs) => ClientType::Tendermint,
            AnyConsensusState::Solomachine(_cs) => ClientType::Solomachine,
            AnyConsensusState::Near(_cs) => ClientType::Near,

            #[cfg(test)]
            AnyConsensusState::Mock(_cs) => ClientType::Mock,
        }
    }
}

impl Protobuf<Any> for AnyConsensusState {}

impl TryFrom<Any> for AnyConsensusState {
    type Error = Error;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        match value.type_url.as_str() {
            "" => Err(Error::empty_consensus_state_response()),

            TENDERMINT_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Tendermint(
                Protobuf::<RawConsensusState>::decode_vec(&value.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),
            SOLOMACHINE_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Solomachine(
                Protobuf::<RawSmConsensusState>::decode_vec(&value.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),
            NEAR_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Near(Box::new(
                Protobuf::<RawNearConsensusState>::decode_vec(&value.value)
                    .map_err(Error::decode_raw_client_state)?,
            ))),

            #[cfg(test)]
            MOCK_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Mock(
                Protobuf::<RawMockConsensusState>::decode_vec(&value.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            _ => Err(Error::unknown_consensus_state_type(value.type_url)),
        }
    }
}

impl From<AnyConsensusState> for Any {
    fn from(value: AnyConsensusState) -> Self {
        match value {
            AnyConsensusState::Tendermint(value) => Any {
                type_url: TENDERMINT_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawConsensusState>::encode_vec(value),
            },
            AnyConsensusState::Solomachine(value) => Any {
                type_url: SOLOMACHINE_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawSmConsensusState>::encode_vec(value),
            },
            AnyConsensusState::Near(value) => Any {
                type_url: NEAR_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawNearConsensusState>::encode_vec(*value),
            },
            #[cfg(test)]
            AnyConsensusState::Mock(value) => Any {
                type_url: MOCK_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawMockConsensusState>::encode_vec(value),
            },
        }
    }
}

#[cfg(test)]
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

impl From<SmConsensusState> for AnyConsensusState {
    fn from(cs: SmConsensusState) -> Self {
        Self::Solomachine(cs)
    }
}

impl From<NearConsensusState> for AnyConsensusState {
    fn from(cs: NearConsensusState) -> Self {
        Self::Near(Box::new(cs))
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
            Self::Solomachine(cs_state) => cs_state.root(),
            Self::Near(cs_state) => cs_state.root(),

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.root(),
        }
    }

    fn timestamp(&self) -> Timestamp {
        AnyConsensusState::timestamp(self)
    }
}
