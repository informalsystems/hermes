#![allow(unreachable_code, unused_variables)]

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics23_commitment::{CommitmentPrefix, CommitmentProof, CommitmentRoot};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use serde_derive::{Deserialize, Serialize};
use tendermint::block::Height;

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
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Box<dyn std::error::Error>> {
        Ok(())
    }

    fn verify_connection_state(
        &self,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Box<dyn std::error::Error>> {
        Ok(())
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
