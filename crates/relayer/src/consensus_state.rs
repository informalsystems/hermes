use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::ConsensusStateWithHeight;
use ibc_proto::ibc::lightclients::tendermint::v1::ConsensusState as RawConsensusState;
#[cfg(test)]
use ibc_proto::ibc::mock::ConsensusState as RawMockConsensusState;
use ibc_proto::protobuf::Protobuf;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::{
    ConsensusState as TmConsensusState, TENDERMINT_CONSENSUS_STATE_TYPE_URL,
};
use ibc_relayer_types::core::ics02_client::client_type::ClientType;
use ibc_relayer_types::core::ics02_client::consensus_state::{
    downcast_consensus_state, ConsensusState,
};
use ibc_relayer_types::core::ics02_client::error::Error;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentRoot;
#[cfg(test)]
use ibc_relayer_types::mock::consensus_state::MockConsensusState;
#[cfg(test)]
use ibc_relayer_types::mock::consensus_state::MOCK_CONSENSUS_STATE_TYPE_URL;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum AnyConsensusState {
    Tendermint(TmConsensusState),

    #[cfg(test)]
    Mock(MockConsensusState),
}

impl AnyConsensusState {
    pub fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(cs_state) => cs_state.timestamp.into(),

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.timestamp(),
        }
    }

    pub fn client_type(&self) -> ClientType {
        match self {
            AnyConsensusState::Tendermint(_cs) => ClientType::Tendermint,

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
                value: Protobuf::<RawConsensusState>::encode_vec(&value)
                    .expect("encoding to `Any` from `AnyConsensusState::Tendermint`"),
            },
            #[cfg(test)]
            AnyConsensusState::Mock(value) => Any {
                type_url: MOCK_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawMockConsensusState>::encode_vec(&value)
                    .expect("encoding to `Any` from `AnyConsensusState::Mock`"),
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

impl From<&dyn ConsensusState> for AnyConsensusState {
    fn from(cs: &dyn ConsensusState) -> Self {
        #[cfg(test)]
        if let Some(cs) = downcast_consensus_state::<MockConsensusState>(cs) {
            return AnyConsensusState::from(cs.clone());
        }

        if let Some(cs) = downcast_consensus_state::<TmConsensusState>(cs) {
            AnyConsensusState::from(cs.clone())
        } else {
            unreachable!()
        }
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

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.root(),
        }
    }

    fn timestamp(&self) -> Timestamp {
        AnyConsensusState::timestamp(self)
    }
}
