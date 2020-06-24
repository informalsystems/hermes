use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::CommitmentRoot;

use crate::ics07_tendermint::error::{Error, Kind};
use crate::ics07_tendermint::header::Header;
use crate::ics24_host::identifier::ClientId;
use serde_derive::{Deserialize, Serialize};
use std::time::Duration;
use tendermint::lite::Header as liteHeader;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ClientState {
    id: ClientId,
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
    ) -> Result<ClientState, Error> {
        // Basic validation of trusting period and unbonding period: each should be non-zero.
        if trusting_period <= Duration::new(0, 0) {
            return Err(Kind::InvalidTrustingPeriod
                .context("ClientState trusting period must be greater than zero")
                .into());
        }
        if unbonding_period <= Duration::new(0, 0) {
            return Err(Kind::InvalidUnboundingPeriod
                .context("ClientState unbonding period must be greater than zero")
                .into());
        }

        // Basic validation for the frozen_height parameter.
        if frozen_height != 0 {
            return Err(Kind::ValidationError
                .context("ClientState cannot be frozen at creation time")
                .into());
        }

        Ok(Self {
            // TODO: Consider adding a specific 'IdentifierError' Kind, akin to the one in ICS04.
            id: id.parse().map_err(|e| Kind::ValidationError.context(e))?,
            trusting_period,
            unbonding_period,
            latest_header,
            frozen_height,
        })
    }
}

impl crate::ics02_client::state::ClientState for ClientState {
    type ValidationError = Error;

    fn client_id(&self) -> ClientId {
        self.id.clone()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn get_latest_height(&self) -> crate::Height {
        self.latest_header.signed_header.header.height()
    }

    fn is_frozen(&self) -> bool {
        // If 'frozen_height' is set to a non-zero value, then the client state is frozen.
        self.frozen_height != 0
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
