use crate::core::ics02_client::client_consensus::{AnyConsensusState, ConsensusState};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::error::Error;


#[derive(Debug, Clone)]
pub struct NearConsensusState {
    commitment_root: CommitmentRoot,
}

impl ConsensusState for NearConsensusState {
    type Error = Error;


    fn client_type(&self) -> ClientType {
        ClientType::Near
    }

    fn root(&self) -> &CommitmentRoot {
        &self.commitment_root
    }

    fn wrap_any(self) -> AnyConsensusState {
        todo!()
    }
}
