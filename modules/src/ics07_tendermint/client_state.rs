use std::convert::{TryFrom, TryInto};
use std::time::Duration;

use ibc_proto::ibc::lightclients::tendermint::v1::{ClientState as RawClientState, Fraction};
use tendermint::consensus::Params;
use tendermint_light_client::types::TrustThreshold;
use tendermint_proto::DomainType;

use crate::Height;

use crate::ics02_client::client_type::ClientType;
use crate::ics07_tendermint::error::{Error, Kind};
use crate::ics23_commitment::merkle::cosmos_specs;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClientState {
    pub chain_id: String,
    pub trust_level: TrustThreshold,
    pub trusting_period: Duration,
    pub unbonding_period: Duration,
    pub max_clock_drift: Duration,
    pub frozen_height: Height,
    pub latest_height: Height,
    pub consensus_params: Params,
    // pub proof_specs: ::std::vec::Vec<super::super::super::super::ics23::ProofSpec>,
    pub upgrade_path: String,
    pub allow_update_after_expiry: bool,
    pub allow_update_after_misbehaviour: bool,
}

impl DomainType<RawClientState> for ClientState {}

impl ClientState {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        chain_id: String,
        trust_level: TrustThreshold,
        trusting_period: Duration,
        unbonding_period: Duration,
        max_clock_drift: Duration,
        latest_height: Height,
        frozen_height: Height,
        consensus_params: Params,
        upgrade_path: String,
        allow_update_after_expiry: bool,
        allow_update_after_misbehaviour: bool, // proof_specs: Specs
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
        if !frozen_height.is_zero() {
            return Err(Kind::ValidationError
                .context("ClientState cannot be frozen at creation time")
                .into());
        }
        // Basic validation for the latest_height parameter.
        if latest_height <= Height::zero() {
            return Err(Kind::ValidationError
                .context("ClientState latest height cannot be smaller or equal than zero")
                .into());
        }

        Ok(Self {
            chain_id,
            trust_level,
            trusting_period,
            unbonding_period,
            max_clock_drift,
            frozen_height,
            latest_height,
            consensus_params,
            upgrade_path,
            allow_update_after_expiry,
            allow_update_after_misbehaviour,
        })
    }
    pub fn latest_height(&self) -> Height {
        self.latest_height
    }
}

impl crate::ics02_client::state::ClientState for ClientState {
    fn chain_id(&self) -> String {
        self.chain_id.clone()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn latest_height(&self) -> Height {
        self.latest_height
    }

    fn is_frozen(&self) -> bool {
        // If 'frozen_height' is set to a non-zero value, then the client state is frozen.
        !self.frozen_height.is_zero()
    }
}

impl TryFrom<RawClientState> for ClientState {
    type Error = Error;

    fn try_from(raw: RawClientState) -> Result<Self, Self::Error> {
        let trust_level = raw
            .trust_level
            .ok_or_else(|| Kind::InvalidRawClientState.context("missing trusting period"))?;

        Ok(Self {
            chain_id: raw.chain_id,
            trust_level: TrustThreshold {
                numerator: trust_level.numerator as u64,
                denominator: trust_level.denominator as u64,
            },
            trusting_period: raw
                .trusting_period
                .ok_or_else(|| Kind::InvalidRawClientState.context("missing trusting period"))?
                .try_into()
                .map_err(|_| Kind::InvalidRawClientState.context("negative trusting period"))?,
            unbonding_period: raw
                .unbonding_period
                .ok_or_else(|| Kind::InvalidRawClientState.context("missing unbonding period"))?
                .try_into()
                .map_err(|_| Kind::InvalidRawClientState.context("negative unbonding period"))?,
            max_clock_drift: raw
                .max_clock_drift
                .ok_or_else(|| Kind::InvalidRawClientState.context("missing max clock drift"))?
                .try_into()
                .map_err(|_| Kind::InvalidRawClientState.context("negative max clock drift"))?,
            latest_height: raw
                .latest_height
                .ok_or_else(|| Kind::InvalidRawClientState.context("missing latest height"))?
                .try_into()
                .map_err(|_| Kind::InvalidRawHeight)?,
            frozen_height: raw
                .frozen_height
                .ok_or_else(|| Kind::InvalidRawClientState.context("missing frozen height"))?
                .try_into()
                .map_err(|_| Kind::InvalidRawHeight)?,
            upgrade_path: raw.upgrade_path,
            allow_update_after_expiry: raw.allow_update_after_expiry,
            allow_update_after_misbehaviour: raw.allow_update_after_misbehaviour,
            consensus_params: raw
                .consensus_params
                .ok_or_else(|| Kind::InvalidRawClientState.context("missing consensus parameters"))?
                .try_into()
                .map_err(|e| Kind::InvalidRawClientState.context(e))?,
        })
    }
}

impl From<ClientState> for RawClientState {
    fn from(value: ClientState) -> Self {
        RawClientState {
            chain_id: value.chain_id.clone(),
            trust_level: Some(Fraction {
                numerator: value.trust_level.numerator as i64,
                denominator: value.trust_level.denominator as i64,
            }),
            trusting_period: Some(value.trusting_period.into()),
            unbonding_period: Some(value.unbonding_period.into()),
            max_clock_drift: Some(value.max_clock_drift.into()),
            frozen_height: Some(value.frozen_height.into()),
            latest_height: Some(value.latest_height.into()),
            consensus_params: Some(value.consensus_params.into()),
            proof_specs: cosmos_specs(),
            allow_update_after_expiry: false,
            allow_update_after_misbehaviour: false,
            upgrade_path: value.upgrade_path,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use tendermint::consensus::Params;
    use tendermint_light_client::types::TrustThreshold;
    use tendermint_rpc::endpoint::abci_query::AbciQuery;

    use crate::ics07_tendermint::client_state::ClientState;
    use crate::test::test_serialization_roundtrip;
    use crate::test_utils::default_consensus_params;
    use crate::Height;

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
            trust_level: TrustThreshold,
            trusting_period: Duration,
            unbonding_period: Duration,
            max_clock_drift: Duration,
            latest_height: Height,
            consensus_params: Params,
            frozen_height: Height,
            upgrade_path: String,
            allow_update_after_expiry: bool,
            allow_update_after_misbehaviour: bool,
        }

        // Define a "default" set of parameters to reuse throughout these tests.
        let default_params: ClientStateParams = ClientStateParams {
            id: "thisisthechainid".to_string(),
            trust_level: TrustThreshold {
                numerator: 1,
                denominator: 3,
            },
            trusting_period: Duration::new(64000, 0),
            unbonding_period: Duration::new(128000, 0),
            max_clock_drift: Duration::new(3, 0),
            latest_height: Height::new(0, 10),
            consensus_params: default_consensus_params(),
            frozen_height: Height::default(),
            upgrade_path: "".to_string(),
            allow_update_after_expiry: false,
            allow_update_after_misbehaviour: false,
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
                name: "Invalid frozen height parameter (should be 0)".to_string(),
                params: ClientStateParams {
                    frozen_height: Height::new(0, 1),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid unbonding period".to_string(),
                params: ClientStateParams {
                    unbonding_period: Duration::default(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid (too small) trusting period".to_string(),
                params: ClientStateParams {
                    trusting_period: Duration::default(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Invalid (too large) trusting period w.r.t. unbonding period".to_string(),
                params: ClientStateParams {
                    trusting_period: Duration::new(11, 0),
                    unbonding_period: Duration::new(10, 0),
                    ..default_params
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
                p.trust_level,
                p.trusting_period,
                p.unbonding_period,
                p.max_clock_drift,
                p.latest_height,
                p.frozen_height,
                p.consensus_params,
                p.upgrade_path,
                p.allow_update_after_expiry,
                p.allow_update_after_misbehaviour,
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

#[cfg(test)]
pub mod test_util {
    use crate::ics02_client::client_def::AnyClientState;
    use crate::ics02_client::height::Height;
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics07_tendermint::header::test_util::get_dummy_tendermint_header;
    use crate::ics24_host::identifier::ChainId;
    use crate::test_utils::default_consensus_params;
    use std::time::Duration;

    pub fn get_dummy_tendermint_client_state() -> AnyClientState {
        let tm_header = get_dummy_tendermint_header();
        AnyClientState::Tendermint(
            ClientState::new(
                tm_header.chain_id.to_string(),
                Default::default(),
                Duration::from_secs(64000),
                Duration::from_secs(128000),
                Duration::from_millis(3000),
                Height::new(
                    ChainId::chain_version(tm_header.chain_id.to_string()),
                    u64::from(tm_header.height),
                ),
                Height::zero(),
                default_consensus_params(),
                "".to_string(),
                false,
                false,
            )
            .unwrap(),
        )
    }
}
