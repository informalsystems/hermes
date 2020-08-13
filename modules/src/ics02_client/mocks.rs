use crate::ics02_client::client::ClientDef;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::handler::ClientReader;
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics23_commitment::CommitmentRoot;
use crate::ics24_host::identifier::ClientId;

use crate::Height;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum MockError {}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MockHeader(pub u32);

impl Header for MockHeader {
    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MockClientState(pub u32);

impl ClientState for MockClientState {
    type ValidationError = MockError;

    fn client_id(&self) -> ClientId {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn get_latest_height(&self) -> Height {
        todo!()
    }

    fn is_frozen(&self) -> bool {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        _root: &CommitmentRoot,
    ) -> Result<(), Self::ValidationError> {
        todo!()
    }
}

impl From<MockConsensusState> for MockClientState {
    fn from(cs: MockConsensusState) -> Self {
        Self(cs.0)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MockConsensusState(pub u32);

impl ConsensusState for MockConsensusState {
    type ValidationError = MockError;

    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
    }

    fn root(&self) -> &CommitmentRoot {
        todo!()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        todo!()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MockClient;

impl ClientDef for MockClient {
    type Error = MockError;
    type Header = MockHeader;
    type ClientState = MockClientState;
    type ConsensusState = MockConsensusState;

    fn check_validity_and_update_state(
        _client_state: &mut MockClientState,
        _consensus_state: &MockConsensusState,
        _header: &MockHeader,
    ) -> Result<(), Self::Error> {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockClientReader {
    pub client_id: ClientId,
    pub client_state: Option<MockClientState>,
    pub client_type: Option<ClientType>,
    pub consensus_state: Option<MockConsensusState>,
}

impl ClientReader<MockClient> for MockClientReader {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType> {
        if client_id == &self.client_id {
            self.client_type.clone()
        } else {
            None
        }
    }

    fn client_state(&self, client_id: &ClientId) -> Option<MockClientState> {
        if client_id == &self.client_id {
            self.client_state
        } else {
            None
        }
    }

    fn consensus_state(&self, client_id: &ClientId, _height: Height) -> Option<MockConsensusState> {
        if client_id == &self.client_id {
            self.consensus_state
        } else {
            None
        }
    }
}
