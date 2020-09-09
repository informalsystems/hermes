#![allow(unreachable_code, unused_variables)]

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof, CommitmentRoot};
use crate::ics23_commitment::merkle::apply_prefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::ics24_host::Path;
use crate::mock_client::header::MockHeader;
use serde_derive::{Deserialize, Serialize};
use tendermint::block::Height;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockClientState(pub MockHeader);

impl MockClientState {
    pub fn check_header_and_update_state(
        &self,
        header: AnyHeader,
    ) -> Result<(MockClientState, MockConsensusState), Box<dyn std::error::Error>> {
        match header {
            #[cfg(test)]
            AnyHeader::Mock(mock_header) => {
                if self.latest_height() >= header.height() {
                    return Err("header height is lower than client latest".into());
                }

                Ok((
                    MockClientState(mock_header),
                    MockConsensusState(mock_header),
                ))
            }
            _ => Err("bad header type for mock client state".into()),
        }
    }
}

#[cfg(test)]
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

    fn latest_height(&self) -> Height {
        self.0.height()
    }

    fn is_frozen(&self) -> bool {
        // TODO
        false
    }
}

impl From<MockConsensusState> for MockClientState {
    fn from(cs: MockConsensusState) -> Self {
        Self(cs.0)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockConsensusState(pub MockHeader);

#[cfg(test)]
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
