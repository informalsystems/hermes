use std::time::Duration;

use serde::{Deserialize, Serialize};

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::IdentifiedClientState;
use ibc_proto::ibc::lightclients::tendermint::v1::ClientState as RawTmClientState;
use ibc_proto::Protobuf;
use ibc_relayer_types::clients::ics07_tendermint::client_state::{
    ClientState as TmClientState, TENDERMINT_CLIENT_STATE_TYPE_URL,
};
use ibc_relayer_types::core::ics02_client::client_state::ClientState;
use ibc_relayer_types::core::ics02_client::client_type::ClientType;
use ibc_relayer_types::core::ics02_client::error::Error;
use ibc_relayer_types::core::ics02_client::trust_threshold::TrustThreshold;
use ibc_relayer_types::core::ics24_host::error::ValidationError;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer_types::Height;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum AnyClientState {
    Tendermint(TmClientState),
}

impl AnyClientState {
    pub fn chain_id(&self) -> ChainId {
        match self {
            AnyClientState::Tendermint(tm_state) => tm_state.chain_id(),
        }
    }

    pub fn latest_height(&self) -> Height {
        match self {
            Self::Tendermint(tm_state) => tm_state.latest_height(),
        }
    }

    pub fn frozen_height(&self) -> Option<Height> {
        match self {
            Self::Tendermint(tm_state) => tm_state.frozen_height(),
        }
    }

    pub fn trust_threshold(&self) -> Option<TrustThreshold> {
        match self {
            AnyClientState::Tendermint(state) => Some(state.trust_threshold),
        }
    }

    pub fn trusting_period(&self) -> Duration {
        match self {
            AnyClientState::Tendermint(state) => state.trusting_period,
        }
    }

    pub fn max_clock_drift(&self) -> Duration {
        match self {
            AnyClientState::Tendermint(state) => state.max_clock_drift,
        }
    }

    pub fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(state) => state.client_type(),
        }
    }

    pub fn expired(&self, elapsed: Duration) -> bool {
        match self {
            Self::Tendermint(state) => state.expired(elapsed),
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
        }
    }
}

impl ClientState for AnyClientState {
    fn chain_id(&self) -> ChainId {
        AnyClientState::chain_id(self)
    }

    fn client_type(&self) -> ClientType {
        AnyClientState::client_type(self)
    }

    fn latest_height(&self) -> Height {
        AnyClientState::latest_height(self)
    }

    fn frozen_height(&self) -> Option<Height> {
        AnyClientState::frozen_height(self)
    }

    fn expired(&self, elapsed: Duration) -> bool {
        AnyClientState::expired(self, elapsed)
    }
}

impl From<TmClientState> for AnyClientState {
    fn from(cs: TmClientState) -> Self {
        Self::Tendermint(cs)
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
