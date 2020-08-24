use crate::ics02_client::client_def::ClientDef;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientState, MockConsensusState};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockClient;

impl ClientDef for MockClient {
    type Header = MockHeader;
    type ClientState = MockClientState;
    type ConsensusState = MockConsensusState;
}
