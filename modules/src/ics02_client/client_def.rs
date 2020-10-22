use prost_types::Any;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;

use crate::downcast;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error;
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics07_tendermint as tendermint;
use crate::ics07_tendermint::client_def::TendermintClient;
use crate::ics07_tendermint::client_state::ClientState as TendermintClientState;
use crate::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof, CommitmentRoot};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::Height;

use tendermint_proto::{DomainType, Error, Kind};

pub const TENDERMINT_CLIENT_STATE_TYPE_URL: &str = "/ibc.lightclients.tendermint.v1.ClientState";
pub const TENDERMINT_CONSENSUS_STATE_TYPE_URL: &str =
    "/ibc.lightclients.tendermint.v1.ConsensusState";
pub const MOCK_CLIENT_STATE_TYPE_URL: &str = "/ibc.mock.ClientState";
pub const MOCK_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.mock.ConsensusState";

#[cfg(test)]
use {
    crate::mock_client::client_def::MockClient,
    crate::mock_client::header::MockHeader,
    crate::mock_client::state::{MockClientState, MockConsensusState},
};

pub trait ClientDef: Clone {
    type Header: Header;
    type ClientState: ClientState;
    type ConsensusState: ConsensusState;

    /// TODO
    fn check_header_and_update_state(
        &self,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Box<dyn std::error::Error>>;

    /// Verification functions as specified in:
    /// https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics
    ///
    /// Verify a `proof` that the consensus state of a given client (at height `consensus_height`)
    /// matches the input `consensus_state`. The parameter `counterparty_height` represent the
    /// height of the counterparty chain that this proof assumes (i.e., the height at which this
    /// proof was computed).
    #[allow(clippy::too_many_arguments)]
    fn verify_client_consensus_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Box<dyn std::error::Error>>;

    /// Verify a `proof` that a connection state matches that of the input `connection_end`.
    fn verify_connection_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Box<dyn std::error::Error>>;

    /// Verify the client state for this chain that it is stored on the counterparty chain.
    #[allow(clippy::too_many_arguments)]
    fn verify_client_full_state(
        &self,
        _client_state: &Self::ClientState,
        height: Height,
        root: &CommitmentRoot,
        prefix: &CommitmentPrefix,
        client_id: &ClientId,
        proof: &CommitmentProof,
        client_state: &AnyClientState,
    ) -> Result<(), Box<dyn std::error::Error>>;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)] // TODO: Add Eq
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Tendermint(tendermint::header::Header),

    #[cfg(test)]
    Mock(MockHeader),
}

impl Header for AnyHeader {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(header) => header.client_type(),

            #[cfg(test)]
            Self::Mock(header) => header.client_type(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(header) => header.height(),

            #[cfg(test)]
            Self::Mock(header) => header.height(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AnyClientState {
    Tendermint(TendermintClientState),

    #[cfg(test)]
    Mock(MockClientState),
}

impl AnyClientState {
    pub fn latest_height(&self) -> Height {
        match self {
            Self::Tendermint(tm_state) => tm_state.latest_height(),

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.latest_height(),
        }
    }
    pub fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(state) => state.client_type(),

            #[cfg(test)]
            Self::Mock(state) => state.client_type(),
        }
    }
}

impl DomainType<Any> for AnyClientState {}

impl TryFrom<Any> for AnyClientState {
    type Error = Error;

    // TODO Fix type urls: avoid having hardcoded values sprinkled around the whole codebase.
    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            TENDERMINT_CLIENT_STATE_TYPE_URL => Ok(AnyClientState::Tendermint(
                TendermintClientState::decode_vec(&raw.value)?,
            )),

            #[cfg(test)]
            MOCK_CLIENT_STATE_TYPE_URL => Ok(AnyClientState::Mock(MockClientState::decode_vec(
                &raw.value,
            )?)),

            _ => Err(Kind::DecodeMessage
                .context(error::Kind::UnknownClientStateType(raw.type_url))
                .into()),
        }
    }
}

impl From<AnyClientState> for Any {
    fn from(value: AnyClientState) -> Self {
        match value {
            AnyClientState::Tendermint(value) => Any {
                type_url: TENDERMINT_CLIENT_STATE_TYPE_URL.to_string(),
                value: value.encode_vec().unwrap(),
            },
            #[cfg(test)]
            AnyClientState::Mock(value) => Any {
                type_url: MOCK_CLIENT_STATE_TYPE_URL.to_string(),
                value: value.encode_vec().unwrap(),
            },
        }
    }
}

impl ClientState for AnyClientState {
    fn chain_id(&self) -> String {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        self.client_type()
    }

    fn latest_height(&self) -> Height {
        self.latest_height()
    }

    fn is_frozen(&self) -> bool {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.is_frozen(),

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => mock_state.is_frozen(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnyConsensusState {
    Tendermint(crate::ics07_tendermint::consensus_state::ConsensusState),

    #[cfg(test)]
    Mock(MockConsensusState),
}

impl AnyConsensusState {
    pub fn client_type(&self) -> ClientType {
        match self {
            AnyConsensusState::Tendermint(_cs) => ClientType::Tendermint,

            #[cfg(test)]
            AnyConsensusState::Mock(_cs) => ClientType::Mock,
        }
    }
}

impl DomainType<Any> for AnyConsensusState {}

impl TryFrom<Any> for AnyConsensusState {
    type Error = Error;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        match value.type_url.as_str() {
            TENDERMINT_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Tendermint(
                TendermintConsensusState::decode_vec(&value.value)?,
            )),

            #[cfg(test)]
            MOCK_CONSENSUS_STATE_TYPE_URL => Ok(AnyConsensusState::Mock(
                MockConsensusState::decode_vec(&value.value)?,
            )),

            _ => Err(Kind::DecodeMessage
                .context(error::Kind::UnknownConsensusStateType(value.type_url))
                .into()),
        }
    }
}

impl From<AnyConsensusState> for Any {
    fn from(value: AnyConsensusState) -> Self {
        match value {
            AnyConsensusState::Tendermint(value) => Any {
                type_url: TENDERMINT_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: value.encode_vec().unwrap(),
            },
            #[cfg(test)]
            AnyConsensusState::Mock(value) => Any {
                type_url: MOCK_CONSENSUS_STATE_TYPE_URL.to_string(),
                value: value.encode_vec().unwrap(),
            },
        }
    }
}

impl ConsensusState for AnyConsensusState {
    fn client_type(&self) -> ClientType {
        self.client_type()
    }

    fn root(&self) -> &CommitmentRoot {
        todo!()
    }

    fn validate_basic(&self) -> Result<(), Box<dyn std::error::Error>> {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnyClient {
    Tendermint(TendermintClient),

    #[cfg(test)]
    Mock(MockClient),
}

impl AnyClient {
    pub fn from_client_type(client_type: ClientType) -> AnyClient {
        match client_type {
            ClientType::Tendermint => Self::Tendermint(TendermintClient),

            #[cfg(test)]
            ClientType::Mock => Self::Mock(MockClient),
        }
    }
}

// ⚠️  Beware of the awful boilerplate below ⚠️
impl ClientDef for AnyClient {
    type Header = AnyHeader;
    type ClientState = AnyClientState;
    type ConsensusState = AnyConsensusState;

    fn check_header_and_update_state(
        &self,
        client_state: AnyClientState,
        header: AnyHeader,
    ) -> Result<(AnyClientState, AnyConsensusState), Box<dyn std::error::Error>> {
        match self {
            Self::Tendermint(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Tendermint,
                    header => AnyHeader::Tendermint,
                )
                .ok_or_else(|| error::Kind::ClientArgsTypeMismatch(ClientType::Tendermint))?;

                let (new_state, new_consensus) =
                    client.check_header_and_update_state(client_state, header)?;

                Ok((
                    AnyClientState::Tendermint(new_state),
                    AnyConsensusState::Tendermint(new_consensus),
                ))
            }

            #[cfg(test)]
            Self::Mock(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Mock,
                    header => AnyHeader::Mock,
                )
                .ok_or_else(|| error::Kind::ClientArgsTypeMismatch(ClientType::Mock))?;

                let (new_state, new_consensus) =
                    client.check_header_and_update_state(client_state, header)?;

                Ok((
                    AnyClientState::Mock(new_state),
                    AnyConsensusState::Mock(new_consensus),
                ))
            }
        }
    }

    fn verify_client_consensus_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Tendermint
                )
                .ok_or_else(|| error::Kind::ClientArgsTypeMismatch(ClientType::Tendermint))?;

                client.verify_client_consensus_state(
                    client_state,
                    height,
                    prefix,
                    proof,
                    client_id,
                    consensus_height,
                    expected_consensus_state,
                )
            }

            #[cfg(test)]
            Self::Mock(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Mock
                )
                .ok_or_else(|| error::Kind::ClientArgsTypeMismatch(ClientType::Mock))?;

                client.verify_client_consensus_state(
                    client_state,
                    height,
                    prefix,
                    proof,
                    client_id,
                    consensus_height,
                    expected_consensus_state,
                )
            }
        }
    }

    fn verify_connection_state(
        &self,
        client_state: &AnyClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(client_state => AnyClientState::Tendermint)
                    .ok_or_else(|| error::Kind::ClientArgsTypeMismatch(ClientType::Tendermint))?;

                client.verify_connection_state(
                    client_state,
                    height,
                    prefix,
                    proof,
                    connection_id,
                    expected_connection_end,
                )
            }

            #[cfg(test)]
            Self::Mock(client) => {
                let client_state = downcast!(client_state => AnyClientState::Mock)
                    .ok_or_else(|| error::Kind::ClientArgsTypeMismatch(ClientType::Mock))?;

                client.verify_connection_state(
                    client_state,
                    height,
                    prefix,
                    proof,
                    connection_id,
                    expected_connection_end,
                )
            }
        }
    }

    fn verify_client_full_state(
        &self,
        client_state: &Self::ClientState,
        height: Height,
        root: &CommitmentRoot,
        prefix: &CommitmentPrefix,
        client_id: &ClientId,
        proof: &CommitmentProof,
        client_state_on_counterparty: &AnyClientState,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Tendermint
                )
                .ok_or_else(|| error::Kind::ClientArgsTypeMismatch(ClientType::Tendermint))?;

                client.verify_client_full_state(
                    client_state,
                    height,
                    root,
                    prefix,
                    client_id,
                    proof,
                    client_state_on_counterparty,
                )
            }

            #[cfg(test)]
            Self::Mock(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Mock
                )
                .ok_or_else(|| error::Kind::ClientArgsTypeMismatch(ClientType::Mock))?;

                client.verify_client_full_state(
                    client_state,
                    height,
                    root,
                    prefix,
                    client_id,
                    proof,
                    client_state_on_counterparty,
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ics02_client::client_def::AnyClientState;
    use crate::ics02_client::height::Height;
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics07_tendermint::header::test_util::get_dummy_header;
    use crate::ics24_host::identifier::ChainId;
    use prost_types::Any;
    use std::convert::TryFrom;
    use std::time::Duration;

    #[test]
    fn to_and_from_any() {
        let tm_header = get_dummy_header();
        let tm_client_state = AnyClientState::Tendermint(ClientState {
            chain_id: tm_header.signed_header.header.chain_id.to_string(),
            trusting_period: Duration::from_secs(64000),
            unbonding_period: Duration::from_secs(128000),
            max_clock_drift: Duration::from_millis(3000),
            latest_height: Height::new(
                ChainId::chain_version(tm_header.signed_header.header.chain_id.to_string()),
                u64::from(tm_header.signed_header.header.height),
            ),
            frozen_height: Height::zero(),
            allow_update_after_expiry: false,
            allow_update_after_misbehaviour: false,
            upgrade_path: "".to_string(),
        });

        let raw: Any = tm_client_state.clone().into();
        let tm_client_state_back = AnyClientState::try_from(raw).unwrap();
        assert_eq!(tm_client_state, tm_client_state_back);
    }
}
