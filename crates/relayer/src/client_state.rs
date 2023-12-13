use core::time::Duration;

use serde::{Deserialize, Serialize};

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::IdentifiedClientState;
use ibc_proto::ibc::lightclients::tendermint::v1::ClientState as RawTmClientState;
use ibc_proto::Protobuf;
use ibc_relayer_types::clients::ics07_tendermint::client_state::{
    ClientState as TmClientState, UpgradeOptions as TmUpgradeOptions,
    TENDERMINT_CLIENT_STATE_TYPE_URL,
};
use ibc_relayer_types::core::ics02_client::client_state::ClientState;
use ibc_relayer_types::core::ics02_client::client_type::ClientType;
use ibc_relayer_types::core::ics02_client::error::Error;
use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;

use ibc_proto::ibc::lightclients::solomachine::v3::ClientState as SmRawClientState;
use ibc_relayer_types::clients::ics06_solomachine::client_state::ClientState as SmClientState;
use ibc_relayer_types::clients::ics06_solomachine::client_state::SOLOMACHINE_CLIENT_STATE_TYPE_URL;
use ibc_relayer_types::clients::ics12_near::client_state::ClientState as NearClientState;
use ibc_relayer_types::clients::ics12_near::client_state::NEAR_CLIENT_STATE_TYPE_URL;
use ibc_relayer_types::core::ics24_host::error::ValidationError;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer_types::Height;

use ics12_proto::v1::ClientState as RawNearClientState;

#[cfg(test)]
use ibc_proto::ibc::mock::ClientState as RawMockClientState;
#[cfg(test)]
use ibc_relayer_types::mock::client_state::MockClientState;
#[cfg(test)]
use ibc_relayer_types::mock::client_state::MOCK_CLIENT_STATE_TYPE_URL;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum AnyUpgradeOptions {
    Tendermint(TmUpgradeOptions),

    #[cfg(test)]
    Mock(()),
}

impl AnyUpgradeOptions {
    fn into_tm_upgrade_options(self) -> Option<TmUpgradeOptions> {
        match self {
            AnyUpgradeOptions::Tendermint(tm) => Some(tm),
            #[cfg(test)]
            AnyUpgradeOptions::Mock(_) => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum AnyClientState {
    Tendermint(TmClientState),
    Solomachine(SmClientState),
    Near(NearClientState),

    #[cfg(test)]
    Mock(MockClientState),
}

impl AnyClientState {
    pub fn chain_id(&self) -> ChainId {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.chain_id(),
            AnyClientState::Solomachine(_sm_state) => todo!(),
            AnyClientState::Near(_near_state) => todo!(),

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => mock_state.chain_id(),
        }
    }

    pub fn latest_height(&self) -> Height {
        match self {
            Self::Tendermint(tm_state) => tm_state.latest_height(),
            Self::Solomachine(sm_state) => sm_state.latest_height(),
            Self::Near(near_state) => near_state.latest_height(),

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.latest_height(),
        }
    }

    pub fn frozen_height(&self) -> Option<Height> {
        match self {
            Self::Tendermint(tm_state) => tm_state.frozen_height(),
            Self::Solomachine(sm_state) => sm_state.frozen_height(),
            Self::Near(near_state) => near_state.frozen_height(),

            #[cfg(test)]
            Self::Mock(mock_state) => mock_state.frozen_height(),
        }
    }

    pub fn trust_threshold(&self) -> Option<TrustThreshold> {
        match self {
            AnyClientState::Tendermint(state) => Some(state.trust_threshold),
            AnyClientState::Solomachine(_state) => Some(TrustThreshold::TWO_THIRDS),
            AnyClientState::Near(_state) => Some(TrustThreshold::TWO_THIRDS),

            #[cfg(test)]
            AnyClientState::Mock(_) => None,
        }
    }

    pub fn max_clock_drift(&self) -> Duration {
        match self {
            AnyClientState::Tendermint(state) => state.max_clock_drift,
            AnyClientState::Solomachine(_state) => Duration::new(0, 0),
            AnyClientState::Near(_state) => Duration::new(6, 0), // TODO: julian

            #[cfg(test)]
            AnyClientState::Mock(_) => Duration::new(0, 0),
        }
    }

    pub fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(state) => state.client_type(),
            Self::Solomachine(state) => state.client_type(),
            Self::Near(state) => state.client_type(),

            #[cfg(test)]
            Self::Mock(state) => state.client_type(),
        }
    }

    pub fn refresh_period(&self) -> Option<Duration> {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.refresh_time(),
            AnyClientState::Solomachine(_sm_state) => None,
            AnyClientState::Near(_sm_state) => None,

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => mock_state.refresh_time(),
        }
    }
}

impl Protobuf<Any> for AnyClientState {}

impl TryFrom<Any> for AnyClientState {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            "" => Err(Error::empty_client_state_response()),

            TENDERMINT_CLIENT_STATE_TYPE_URL => Ok(AnyClientState::Tendermint(
                Protobuf::<RawTmClientState>::decode_vec(&raw.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            SOLOMACHINE_CLIENT_STATE_TYPE_URL => Ok(AnyClientState::Solomachine(
                Protobuf::<SmRawClientState>::decode_vec(&raw.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),
            NEAR_CLIENT_STATE_TYPE_URL => Ok(AnyClientState::Near(
                Protobuf::<RawNearClientState>::decode_vec(&raw.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            #[cfg(test)]
            MOCK_CLIENT_STATE_TYPE_URL => Ok(AnyClientState::Mock(
                Protobuf::<RawMockClientState>::decode_vec(&raw.value)
                    .map_err(Error::decode_raw_client_state)?,
            )),

            _ => Err(Error::unknown_client_state_type(raw.type_url)),
        }
    }
}

impl From<AnyClientState> for Any {
    fn from(value: AnyClientState) -> Self {
        match value {
            AnyClientState::Tendermint(value) => Any {
                type_url: TENDERMINT_CLIENT_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawTmClientState>::encode_vec(value),
            },
            AnyClientState::Solomachine(value) => Any {
                type_url: SOLOMACHINE_CLIENT_STATE_TYPE_URL.to_string(),
                value: Protobuf::<SmRawClientState>::encode_vec(value),
            },
            AnyClientState::Near(value) => Any {
                type_url: NEAR_CLIENT_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawNearClientState>::encode_vec(value),
            },
            #[cfg(test)]
            AnyClientState::Mock(value) => Any {
                type_url: MOCK_CLIENT_STATE_TYPE_URL.to_string(),
                value: Protobuf::<RawMockClientState>::encode_vec(value),
            },
        }
    }
}

impl ClientState for AnyClientState {
    type UpgradeOptions = AnyUpgradeOptions;

    fn chain_id(&self) -> ChainId {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.chain_id(),
            AnyClientState::Solomachine(sm_state) => sm_state.chain_id(),
            AnyClientState::Near(near_state) => near_state.chain_id(),

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => mock_state.chain_id(),
        }
    }

    fn client_type(&self) -> ClientType {
        self.client_type()
    }

    fn latest_height(&self) -> Height {
        self.latest_height()
    }

    fn frozen_height(&self) -> Option<Height> {
        self.frozen_height()
    }

    fn upgrade(
        &mut self,
        upgrade_height: Height,
        upgrade_options: AnyUpgradeOptions,
        chain_id: ChainId,
    ) {
        match self {
            AnyClientState::Tendermint(tm_state) => {
                if let Some(upgrade_options) = upgrade_options.into_tm_upgrade_options() {
                    tm_state.upgrade(upgrade_height, upgrade_options, chain_id);
                }
                // TODO: Handle case where upgrade options are not of the right type,
                //       not a problem in practice for now but good to have.
            }
            AnyClientState::Solomachine(_sm_state) => (),
            AnyClientState::Near(_near_state) => (),

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => {
                mock_state.upgrade(upgrade_height, (), chain_id);
            }
        }
    }

    fn expired(&self, elapsed_since_latest: Duration) -> bool {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.expired(elapsed_since_latest),
            AnyClientState::Solomachine(_sm_state) => false,
            AnyClientState::Near(_near_state) => false,

            #[cfg(test)]
            AnyClientState::Mock(mock_state) => mock_state.expired(elapsed_since_latest),
        }
    }
}

impl From<TmClientState> for AnyClientState {
    fn from(cs: TmClientState) -> Self {
        Self::Tendermint(cs)
    }
}

impl From<SmClientState> for AnyClientState {
    fn from(cs: SmClientState) -> Self {
        Self::Solomachine(cs)
    }
}

impl From<NearClientState> for AnyClientState {
    fn from(cs: NearClientState) -> Self {
        Self::Near(cs)
    }
}

#[cfg(test)]
impl From<MockClientState> for AnyClientState {
    fn from(cs: MockClientState) -> Self {
        Self::Mock(cs)
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub struct IdentifiedAnyClientState {
    pub client_id: ClientId,
    pub client_state: AnyClientState,
}

impl IdentifiedAnyClientState {
    pub fn new(client_id: ClientId, client_state: AnyClientState) -> Self {
        IdentifiedAnyClientState {
            client_id,
            client_state,
        }
    }
}

impl Protobuf<IdentifiedClientState> for IdentifiedAnyClientState {}

impl TryFrom<IdentifiedClientState> for IdentifiedAnyClientState {
    type Error = Error;

    fn try_from(raw: IdentifiedClientState) -> Result<Self, Self::Error> {
        Ok(IdentifiedAnyClientState {
            client_id: raw.client_id.parse().map_err(|e: ValidationError| {
                Error::invalid_raw_client_id(raw.client_id.clone(), e)
            })?,
            client_state: raw
                .client_state
                .ok_or_else(Error::missing_raw_client_state)?
                .try_into()?,
        })
    }
}

impl From<IdentifiedAnyClientState> for IdentifiedClientState {
    fn from(value: IdentifiedAnyClientState) -> Self {
        IdentifiedClientState {
            client_id: value.client_id.to_string(),
            client_state: Some(value.client_state.into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use ibc_proto::google::protobuf::Any;
    use ibc_relayer_types::clients::ics07_tendermint::client_state::test_util::get_dummy_tendermint_client_state;
    use ibc_relayer_types::clients::ics07_tendermint::header::test_util::get_dummy_tendermint_header;
    use test_log::test;

    use super::AnyClientState;

    #[test]
    fn any_client_state_serialization() {
        let tm_client_state: AnyClientState =
            get_dummy_tendermint_client_state(get_dummy_tendermint_header()).into();

        let raw: Any = tm_client_state.clone().into();
        let tm_client_state_back = AnyClientState::try_from(raw).unwrap();
        assert_eq!(tm_client_state, tm_client_state_back);
    }
}
