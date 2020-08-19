use serde_derive::{Deserialize, Serialize};

use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics23_commitment::CommitmentRoot;
use crate::Height;

use crate::ics02_client::mocks;
use crate::ics07_tendermint as tendermint;
use crate::ics07_tendermint::client_def::TendermintClient;

pub trait ClientDef: Clone {
    type Header: Header;
    type ClientState: ClientState;
    type ConsensusState: ConsensusState;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)] // TODO: Add Eq
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Mock(mocks::MockHeader),
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
    Mock(mocks::MockClientState),
    Tendermint(crate::ics07_tendermint::client_state::ClientState),
}

impl ClientState for AnyClientState {
    fn chain_id(&self) -> String {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn get_latest_height(&self) -> Height {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.get_latest_height(),
            AnyClientState::Mock(mock_state) => mock_state.get_latest_height(),
        }
    }

    fn is_frozen(&self) -> bool {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        _root: &CommitmentRoot,
    ) -> Result<(), Box<dyn std::error::Error>> {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum AnyConsensusState {
    Mock(mocks::MockConsensusState),
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
    Mock(mocks::MockClient),
    Tendermint(TendermintClient),
}

impl ClientDef for AnyClient {
    type Header = AnyHeader;
    type ClientState = AnyClientState;
    type ConsensusState = AnyConsensusState;
}
