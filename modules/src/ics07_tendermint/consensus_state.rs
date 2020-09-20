use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::commitment::CommitmentRoot;

use serde_derive::{Deserialize, Serialize};
use tendermint::Hash;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConsensusState {
    pub height: crate::Height,
    pub timestamp: tendermint::time::Time,
    pub root: CommitmentRoot,
    pub next_validators_hash: Hash,
}

impl ConsensusState {
    pub fn new(
        root: CommitmentRoot,
        height: crate::Height,
        timestamp: tendermint::time::Time,
        next_validators_hash: Hash,
    ) -> Self {
        Self {
            root,
            height,
            timestamp,
            next_validators_hash,
        }
    }
}

impl crate::ics02_client::state::ConsensusState for ConsensusState {
    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn height(&self) -> crate::Height {
        self.height
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn validate_basic(&self) -> Result<(), Box<dyn std::error::Error>> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use crate::test::test_serialization_roundtrip;
    use tendermint_rpc::endpoint::abci_query::AbciQuery;

    #[test]
    fn serialization_roundtrip_no_proof() {
        let json_data =
            include_str!("../../tests/support/query/serialization/consensus_state.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn serialization_roundtrip_with_proof() {
        let json_data =
            include_str!("../../tests/support/query/serialization/consensus_state_proof.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }
}
