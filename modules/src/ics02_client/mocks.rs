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
    ) -> Result<(), Box<dyn std::error::Error>> {
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
pub struct MockClientReader {
    pub client_id: ClientId,
    pub client_state: Option<MockClientState>,
    pub client_type: Option<ClientType>,
    pub consensus_state: Option<MockConsensusState>,
}

impl ClientReader for MockClientReader {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType> {
        if client_id == &self.client_id {
            self.client_type.clone()
        } else {
            None
        }
    }

    #[allow(trivial_casts)]
    fn client_state(&self, client_id: &ClientId) -> Option<Box<dyn ClientState>> {
        if client_id == &self.client_id {
            self.client_state.map(|cs| Box::new(cs) as _)
        } else {
            None
        }
    }

    #[allow(trivial_casts)]
    fn consensus_state(
        &self,
        client_id: &ClientId,
        _height: Height,
    ) -> Option<Box<dyn ConsensusState>> {
        if client_id == &self.client_id {
            self.consensus_state.map(|cs| Box::new(cs) as _)
        } else {
            None
        }
    }
}
