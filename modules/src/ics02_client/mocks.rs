use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader, ClientDef};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics02_client::handler::{ClientKeeper, ClientReader};
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics23_commitment::CommitmentRoot;
use crate::ics24_host::identifier::ClientId;
use crate::Height;

use serde_derive::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum MockError {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockHeader(pub u32);

impl From<MockHeader> for AnyHeader {
    fn from(mh: MockHeader) -> Self {
        Self::Mock(mh)
    }
}

impl Header for MockHeader {
    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockClientState(pub u32);

impl From<MockClientState> for AnyClientState {
    fn from(mcs: MockClientState) -> Self {
        Self::Mock(mcs)
    }
}

impl ClientState for MockClientState {
    fn chain_id(&self) -> String {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn get_latest_height(&self) -> Height {
        Height::from(self.0 as u64)
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockConsensusState(pub u32);

impl From<MockConsensusState> for AnyConsensusState {
    fn from(mcs: MockConsensusState) -> Self {
        Self::Mock(mcs)
    }
}

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
pub struct MockClient;

impl ClientDef for MockClient {
    type Header = MockHeader;
    type ClientState = MockClientState;
    type ConsensusState = MockConsensusState;
}

#[derive(Clone, Debug, PartialEq)]
pub struct MockClientContext {
    reader: MockClientReader,
    keeper: MockClientKeeper,
}

#[derive(Clone, Debug, PartialEq)]
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
    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        if client_id == &self.client_id {
            self.client_state.map(Into::into)
        } else {
            None
        }
    }

    #[allow(trivial_casts)]
    fn consensus_state(&self, client_id: &ClientId, _height: Height) -> Option<AnyConsensusState> {
        if client_id == &self.client_id {
            self.consensus_state.map(Into::into)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct MockClientKeeper {
    pub client_state: Option<MockClientState>,
    pub client_type: Option<ClientType>,
    pub consensus_state: Option<MockConsensusState>,
}

impl ClientKeeper for MockClientKeeper {
    fn store_client_type(
        &mut self,
        _client_id: ClientId,
        _client_type: ClientType,
    ) -> Result<(), Error> {
        todo!()
    }

    fn store_client_state(
        &mut self,
        _client_id: ClientId,
        _client_state: AnyClientState,
    ) -> Result<(), Error> {
        todo!()
    }

    fn store_consensus_state(
        &mut self,
        _client_id: ClientId,
        _consensus_state: AnyConsensusState,
    ) -> Result<(), Error> {
        todo!()
    }
}
