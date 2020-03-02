use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::CommitmentRoot;

use serde_derive::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConsensusState {
    root: CommitmentRoot,
    height: crate::Height,
    timestamp: tendermint::time::Time,
    validator_set: tendermint::validator::Set,
}

impl ConsensusState {
    pub fn new(
        root: CommitmentRoot,
        height: crate::Height,
        timestamp: tendermint::time::Time,
        validator_set: tendermint::validator::Set,
    ) -> Self {
        Self {
            root,
            height,
            timestamp,
            validator_set,
        }
    }
}

impl crate::ics02_client::state::ConsensusState for ConsensusState {
    type ValidationError = crate::ics07_tendermint::error::Error;

    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn height(&self) -> crate::Height {
        self.height
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        unimplemented!()
    }
}
