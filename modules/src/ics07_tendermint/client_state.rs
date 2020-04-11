use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::CommitmentRoot;

use crate::ics07_tendermint::header::Header;
use crate::ics24_host::client::ClientId;
use serde_derive::{Deserialize, Serialize};
use std::time::Duration;
use tendermint::lite::Header as liteHeader;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ClientState {
    id: String,
    trusting_period: Duration,
    unbonding_period: Duration,
    frozen_height: crate::Height,
    latest_header: Header,
}

impl ClientState {
    pub fn new(
        id: String,
        trusting_period: Duration,
        unbonding_period: Duration,
        latest_header: Header,
        frozen_height: crate::Height,
    ) -> Self {
        Self {
            id,
            trusting_period,
            unbonding_period,
            latest_header,
            frozen_height,
        }
    }
}

impl crate::ics02_client::state::ClientState for ClientState {
    type ValidationError = crate::ics07_tendermint::error::Error;

    fn client_id(&self) -> ClientId {
        self.id.parse().unwrap()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn get_latest_height(&self) -> crate::Height {
        self.latest_header.signed_header.header.height()
    }

    fn is_frozen(&self) -> bool {
        false
    }

    fn verify_client_consensus_state(
        &self,
        _root: &CommitmentRoot,
    ) -> Result<(), Self::ValidationError> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use crate::test::test_serialization_roundtrip;
    use tendermint::rpc::endpoint::abci_query::AbciQuery;

    #[test]
    fn serialization_roundtrip_no_proof() {
        let json_data = include_str!("../tests/query/serialization/client_state.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn serialization_roundtrip_with_proof() {
        let json_data = include_str!("../tests/query/serialization/client_state_proof.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }
}
