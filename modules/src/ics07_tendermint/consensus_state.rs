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

#[cfg(test)]
mod tests {
    use crate::test::test_serialization_roundtrip;
    use tendermint_rpc::endpoint::abci_query::AbciQuery;

    #[test]
    fn serialization_roundtrip_no_proof() {
        let json_data = include_str!("../tests/query/serialization/consensus_state.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn serialization_roundtrip_with_proof() {
        let json_data = include_str!("../tests/query/serialization/consensus_state_proof.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }
}
