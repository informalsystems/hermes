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
        if trusting_period >= unbonding_period {
            return Err(Kind::InvalidUnboundingPeriod
                .context("ClientState trusting period must be smaller than unbonding period")
                .into());
        }

        // Basic validation for the frozen_height parameter.
        if frozen_height != 0 {
            return Err(Kind::ValidationError
                .context("ClientState cannot be frozen at creation time")
                .into());
        }

        // Initially, no validation is needed for the `latest_header`. This has to be validated
        // upon updating a client (see `update_client.rs` and fn
        // `ClientState::verify_client_consensus_state`).

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
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics07_tendermint::header::test_util::get_dummy_header;
    use crate::ics07_tendermint::header::Header;
    use crate::test::test_serialization_roundtrip;
    use std::time::Duration;
    use tendermint_rpc::endpoint::abci_query::AbciQuery;

    #[test]
    fn serialization_roundtrip_no_proof() {
        let json_data = include_str!("../../tests/support/query/serialization/client_state.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn serialization_roundtrip_with_proof() {
        let json_data =
            include_str!("../../tests/support/query/serialization/client_state_proof.json");
        println!("json_data: {:?}", json_data);
        test_serialization_roundtrip::<AbciQuery>(json_data);
    }

    #[test]
    fn client_state_new() {
        #[derive(Clone, Debug, PartialEq)]
        struct ClientStateParams {
            id: String,
            trusting_period: Duration,
            unbonding_period: Duration,
            latest_header: Header,
            frozen_height: crate::Height,
        }

        // Define a "default" set of parameters to reuse throughout these tests.
        let default_params: ClientStateParams = ClientStateParams {
            id: "abcdefghijkl".to_string(),
            trusting_period: Duration::from_secs(64000),
            unbonding_period: Duration::from_secs(128000),
            latest_header: get_dummy_header(),
            frozen_height: 0,
        };

        struct Test {
            name: String,
            params: ClientStateParams,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Valid parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Invalid client id".to_string(),
                params: ClientStateParams {
                    id: "9000".to_string(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid frozen height parameter (should be 0)".to_string(),
                params: ClientStateParams {
                    frozen_height: 1,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid unbonding period".to_string(),
                params: ClientStateParams {
                    unbonding_period: Duration::from_secs(0),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid (too small) trusting period".to_string(),
                params: ClientStateParams {
                    trusting_period: Duration::from_secs(0),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid (too large) trusting period w.r.t. unbonding period".to_string(),
                params: ClientStateParams {
                    trusting_period: Duration::from_secs(11),
                    unbonding_period: Duration::from_secs(10),
                    ..default_params.clone()
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let cs_result = ClientState::new(
                p.id,
                p.trusting_period,
                p.unbonding_period,
                p.latest_header,
                p.frozen_height,
            );

            assert_eq!(
                test.want_pass,
                cs_result.is_ok(),
                "ClientState::new() failed for test {}, \nmsg{:?} with error {:?}",
                test.name,
                test.params.clone(),
                cs_result.err(),
            );
        }
    }
}
