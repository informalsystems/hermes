use crate::prelude::*;

use core::convert::Infallible;
use core::fmt::Debug;
use core::marker::{Send, Sync};

use crate::clients::crypto_ops::crypto::CryptoOps;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::ConsensusStateWithHeight;
use serde::Serialize;
use tendermint_proto::Protobuf;

use crate::clients::ics07_tendermint::consensus_state;
use crate::clients::ics11_beefy::consensus_state as beefy_consensus_state;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::height::Height;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::core::ics24_host::identifier::ClientId;
use crate::events::WithBlockDataType;
use crate::timestamp::Timestamp;

#[cfg(any(test, feature = "mocks"))]
use crate::mock::client_state::MockConsensusState;

pub const TENDERMINT_CONSENSUS_STATE_TYPE_URL: &str =
    "/ibc.lightclients.tendermint.v1.ConsensusState";

pub const BEEFY_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.lightclients.beefy.v1.ConsensusState";

pub const MOCK_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.mock.ConsensusState";

pub trait ConsensusState: Clone + Send + Sync {
    type Error;
    type Crypto: CryptoOps;

    /// Type of client associated with this consensus state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Commitment root of the consensus state, which is used for key-value pair verification.
    fn root(&self) -> &CommitmentRoot;

    /// Wrap into an `AnyConsensusState`
    fn wrap_any(self) -> AnyConsensusState<Self::Crypto>;
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "type")]
pub enum AnyConsensusState<Crypto> {
    Tendermint(consensus_state::ConsensusState<Crypto>),
    Beefy(beefy_consensus_state::ConsensusState<Crypto>),
    #[cfg(any(test, feature = "mocks"))]
    Mock(MockConsensusState<Crypto>),
}

impl<Crypto> AnyConsensusState<Crypto> {
    pub fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(cs_state) => cs_state.timestamp.into(),
            Self::Beefy(cs_state) => cs_state.timestamp.into(),
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(mock_state) => mock_state.timestamp(),
        }
    }

    pub fn client_type(&self) -> ClientType {
        match self {
            AnyConsensusState::Tendermint(_cs) => ClientType::Tendermint,
            AnyConsensusState::Beefy(_) => ClientType::Beefy,
            #[cfg(any(test, feature = "mocks"))]
            AnyConsensusState::Mock(_cs) => ClientType::Mock,
        }
    }
}

impl<Crypto: Clone> Protobuf<Any> for AnyConsensusState<Crypto> {}

impl<Crypto: Clone> TryFrom<Any> for AnyConsensusState<Crypto> {
    type Error = Error;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        match value.type_url.as_str() {
            "" => Err(Error::empty_consensus_state_response()),

            TENDERMINT_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Tendermint(
                consensus_state::ConsensusState::decode_vec(&value.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            BEEFY_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Beefy(
                beefy_consensus_state::ConsensusState::decode_vec(&value.value)
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

impl<Crypto: Clone> From<AnyConsensusState<Crypto>> for Any {
    fn from(value: AnyConsensusState<Crypto>) -> Self {
        match value {
            AnyConsensusState::Tendermint(value) => Any {
                type_url: TENDERMINT_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: value
                    .encode_vec()
                    .expect("encoding to `Any` from `AnyConsensusState::Tendermint`"),
            },

            AnyConsensusState::Beefy(value) => Any {
                type_url: BEEFY_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: value
                    .encode_vec()
                    .expect("encoding to `Any` from `AnyConsensusState::Beefy`"),
            },
            #[cfg(any(test, feature = "mocks"))]
            AnyConsensusState::Mock(value) => Any {
                type_url: MOCK_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: value
                    .encode_vec()
                    .expect("encoding to `Any` from `AnyConsensusState::Mock`"),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AnyConsensusStateWithHeight<Crypto> {
    pub height: Height,
    pub consensus_state: AnyConsensusState<Crypto>,
}

impl<Crypto: Clone> Protobuf<ConsensusStateWithHeight> for AnyConsensusStateWithHeight<Crypto> {}

impl<Crypto: Clone> TryFrom<ConsensusStateWithHeight> for AnyConsensusStateWithHeight<Crypto> {
    type Error = Error;

    fn try_from(value: ConsensusStateWithHeight) -> Result<Self, Self::Error> {
        let state = value
            .consensus_state
            .map(AnyConsensusState::try_from)
            .transpose()?
            .ok_or_else(Error::empty_consensus_state_response)?;

        Ok(AnyConsensusStateWithHeight {
            height: value.height.ok_or_else(Error::missing_height)?.into(),
            consensus_state: state,
        })
    }
}

impl<Crypto: Clone> From<AnyConsensusStateWithHeight<Crypto>> for ConsensusStateWithHeight {
    fn from(value: AnyConsensusStateWithHeight<Crypto>) -> Self {
        ConsensusStateWithHeight {
            height: Some(value.height.into()),
            consensus_state: Some(value.consensus_state.into()),
        }
    }
}

impl<Crypto: CryptoOps + Debug + Send + Sync> ConsensusState for AnyConsensusState<Crypto> {
    type Crypto = Crypto;
    type Error = Infallible;

    fn client_type(&self) -> ClientType {
        self.client_type()
    }

    fn root(&self) -> &CommitmentRoot {
        match self {
            Self::Tendermint(cs_state) => cs_state.root(),
            Self::Beefy(cs_state) => cs_state.root(),
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(mock_state) => mock_state.root(),
        }
    }

    fn wrap_any(self) -> AnyConsensusState<Self::Crypto> {
        self
    }
}

/// Query request for a single client event, identified by `event_id`, for `client_id`.
#[derive(Clone, Debug)]
pub struct QueryClientEventRequest {
    pub height: crate::Height,
    pub event_id: WithBlockDataType,
    pub client_id: ClientId,
    pub consensus_height: crate::Height,
}
