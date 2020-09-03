use serde_derive::{Deserialize, Serialize};

use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof, CommitmentRoot};
use crate::Height;

use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics07_tendermint as tendermint;
use crate::ics07_tendermint::client_def::TendermintClient;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::mock_client::client_def::MockClient;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientState, MockConsensusState};

pub trait ClientDef: Clone {
    type Header: Header;
    type ClientState: ClientState;
    type ConsensusState: ConsensusState;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)] // TODO: Add Eq
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Mock(MockHeader),
    Tendermint(tendermint::header::Header),
}

impl Header for AnyHeader {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Mock(header) => header.client_type(),
            Self::Tendermint(header) => header.client_type(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Mock(header) => header.height(),
            Self::Tendermint(header) => header.height(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum AnyClientState {
    Mock(MockClientState),
    Tendermint(crate::ics07_tendermint::client_state::ClientState),
}

impl AnyClientState {
    pub fn check_header_and_update_state(
        &self,
        header: AnyHeader,
    ) -> Result<(AnyClientState, AnyConsensusState), Box<dyn std::error::Error>> {
        match self {
            AnyClientState::Tendermint(tm_state) => {
                let (new_state, new_consensus) = tm_state.check_header_and_update_state(header)?;
                Ok((
                    AnyClientState::Tendermint(new_state),
                    AnyConsensusState::Tendermint(new_consensus),
                ))
            }
            AnyClientState::Mock(mock_state) => {
                let (new_state, new_consensus) =
                    mock_state.check_header_and_update_state(header)?;
                Ok((
                    AnyClientState::Mock(new_state),
                    AnyConsensusState::Mock(new_consensus),
                ))
            }
        }
    }
}

impl ClientState for AnyClientState {
    fn chain_id(&self) -> String {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn latest_height(&self) -> Height {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.latest_height(),
            AnyClientState::Mock(mock_state) => mock_state.latest_height(),
        }
    }

    fn is_frozen(&self) -> bool {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.is_frozen(),
            AnyClientState::Mock(mock_state) => mock_state.is_frozen(),
        }
    }

    // fn check_header_and_update_state(
    //     &self,
    //     header: &dyn Header,
    // ) -> Result<(Box<dyn ClientState>, Box<dyn ConsensusState>), Box<dyn std::error::Error>> {
    //     match self {
    //         AnyClientState::Tendermint(tm_state) => tm_state.check_header_and_update_state(header),
    //         AnyClientState::Mock(mock_state) => mock_state.check_header_and_update_state(header),
    //     }
    // }

    fn verify_client_consensus_state(
        &self,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.verify_client_consensus_state(
                height,
                prefix,
                proof,
                client_id,
                consensus_height,
                expected_consensus_state,
            ),
            AnyClientState::Mock(mock_state) => mock_state.verify_client_consensus_state(
                height,
                prefix,
                proof,
                client_id,
                consensus_height,
                expected_consensus_state,
            ),
        }
    }

    fn verify_connection_state(
        &self,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.verify_connection_state(
                height,
                prefix,
                proof,
                connection_id,
                expected_connection_end,
            ),
            AnyClientState::Mock(mock_state) => mock_state.verify_connection_state(
                height,
                prefix,
                proof,
                connection_id,
                expected_connection_end,
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum AnyConsensusState {
    Mock(MockConsensusState),
    Tendermint(crate::ics07_tendermint::consensus_state::ConsensusState),
}

impl ConsensusState for AnyConsensusState {
    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
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
    Mock(MockClient),
    Tendermint(TendermintClient),
}

impl ClientDef for AnyClient {
    type Header = AnyHeader;
    type ClientState = AnyClientState;
    type ConsensusState = AnyConsensusState;
}
