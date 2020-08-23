use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::error::Error;
use crate::ics02_client::mocks::{MockClientState, MockConsensusState};
use crate::ics24_host::identifier::ClientId;
use tendermint::block::Height;

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
