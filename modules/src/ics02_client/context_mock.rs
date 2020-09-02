use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::error::Error;
use crate::ics24_host::identifier::ClientId;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientState, MockConsensusState};
use tendermint::block::Height;

#[derive(Clone, Debug, PartialEq)]
pub struct MockClientContext {
    pub client_id: ClientId,
    pub client_state: Option<MockClientState>,
    pub client_type: Option<ClientType>,
    pub consensus_state: Option<MockConsensusState>,
}

impl Default for MockClientContext {
    fn default() -> Self {
        MockClientContext {
            client_id: "defaultclientid".to_string().parse().unwrap(),
            client_state: None,
            client_type: None,
            consensus_state: None,
        }
    }
}

impl MockClientContext {
    pub fn new(client_id: &ClientId) -> Self {
        MockClientContext {
            client_id: client_id.clone(),
            client_type: None,
            client_state: None,
            consensus_state: None,
        }
    }

    pub fn with_client_type(&mut self, client_type: ClientType) {
        self.client_type = Option::from(client_type);
    }

    pub fn with_client_state(&mut self, client_id: &ClientId, h: u64) {
        self.client_id = client_id.clone();
        self.client_type = Option::from(ClientType::Mock);
        self.client_state = Option::from(MockClientState(MockHeader(Height(h))));
        self.consensus_state = Option::from(MockConsensusState(MockHeader(Height(h))));
    }
}

impl ClientReader for MockClientContext {
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

impl ClientKeeper for MockClientContext {
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
