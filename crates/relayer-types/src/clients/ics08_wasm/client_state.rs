//! Defines the client state type for the ICS-08 Wasm light client.

use std::time::Duration;

use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};

use crate::clients::ics07_tendermint::client_state::ClientState as TmClientState;
use crate::core::ics02_client::client_state::ClientState as Ics02ClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics02_client::height::Height;
use crate::core::ics02_client::trust_threshold::TrustThreshold;
use crate::core::ics24_host::identifier::ChainId;

use super::error::Error;
use super::proto::v1::ClientState as RawClientState;

pub const WASM_CLIENT_STATE_TYPE_URL: &str = "/ibc.lightclients.wasm.v1.ClientState";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum WasmUnderlyingClientState {
    Tendermint(TmClientState),
}

impl Ics02ClientState for WasmUnderlyingClientState {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(tm_client_state) => tm_client_state.client_type(),
        }
    }

    fn chain_id(&self) -> ChainId {
        match self {
            Self::Tendermint(tm_client_state) => tm_client_state.chain_id(),
        }
    }

    fn latest_height(&self) -> Height {
        match self {
            Self::Tendermint(tm_client_state) => tm_client_state.latest_height(),
        }
    }

    fn frozen_height(&self) -> Option<Height> {
        match self {
            Self::Tendermint(tm_client_state) => tm_client_state.frozen_height(),
        }
    }

    fn expired(&self, elapsed: Duration) -> bool {
        match self {
            Self::Tendermint(tm_client_state) => tm_client_state.expired(elapsed),
        }
    }
}

/// The Wasm client state tracks the location of the Wasm bytecode via codeHash.
/// Binary data represented by the data field is opaque and only interpreted by the Wasm contract.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ClientState {
    pub checksum: Vec<u8>,
    pub latest_height: Height,
    pub underlying: WasmUnderlyingClientState,
}

impl ClientState {
    pub const TYPE_URL: &'static str = WASM_CLIENT_STATE_TYPE_URL;

    pub fn trust_threshold(&self) -> Option<TrustThreshold> {
        match &self.underlying {
            WasmUnderlyingClientState::Tendermint(tm) => Some(tm.trust_threshold),
        }
    }

    pub fn trusting_period(&self) -> Duration {
        match &self.underlying {
            WasmUnderlyingClientState::Tendermint(tm) => tm.trusting_period,
        }
    }

    pub fn max_clock_drift(&self) -> Duration {
        match &self.underlying {
            WasmUnderlyingClientState::Tendermint(tm) => tm.max_clock_drift,
        }
    }
}

impl Ics02ClientState for ClientState {
    fn client_type(&self) -> ClientType {
        ClientType::Wasm
    }

    fn chain_id(&self) -> ChainId {
        self.underlying.chain_id()
    }

    fn latest_height(&self) -> Height {
        self.latest_height
    }

    fn frozen_height(&self) -> Option<Height> {
        self.underlying.frozen_height()
    }

    fn expired(&self, elapsed: Duration) -> bool {
        self.underlying.expired(elapsed)
    }
}

fn encode_underlying_client_state(client_state: WasmUnderlyingClientState) -> Vec<u8> {
    match client_state {
        WasmUnderlyingClientState::Tendermint(tm_client_state) => {
            Any::from(tm_client_state).encode_to_vec()
        }
    }
}

fn decode_underlying_client_state(data: &[u8]) -> Result<WasmUnderlyingClientState, Error> {
    let any = Any::decode(data)?;
    match any.type_url.as_str() {
        TmClientState::TYPE_URL => {
            let tm_client_state = TmClientState::try_from(any)?;
            Ok(WasmUnderlyingClientState::Tendermint(tm_client_state))
        }
        _ => Err(Error::unsupported_wasm_client_state_type(any.type_url)),
    }
}

impl Protobuf<RawClientState> for ClientState {}

impl From<ClientState> for RawClientState {
    fn from(value: ClientState) -> Self {
        RawClientState {
            data: encode_underlying_client_state(value.underlying),
            checksum: value.checksum,
            latest_height: Some(value.latest_height.into()),
        }
    }
}

impl TryFrom<RawClientState> for ClientState {
    type Error = Error;

    fn try_from(value: RawClientState) -> Result<Self, Self::Error> {
        let raw_height = value
            .latest_height
            .ok_or_else(Error::missing_latest_height)?;

        Ok(ClientState {
            checksum: value.checksum,
            latest_height: raw_height
                .try_into()
                .map_err(|_| Error::invalid_raw_height(raw_height))?,
            underlying: decode_underlying_client_state(&value.data)?,
        })
    }
}

impl Protobuf<Any> for ClientState {}

impl TryFrom<Any> for ClientState {
    type Error = Ics02Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        use bytes::Buf;
        use core::ops::Deref;

        fn decode_client_state<B: Buf>(buf: B) -> Result<ClientState, Error> {
            RawClientState::decode(buf)?.try_into()
        }

        match raw.type_url.as_str() {
            WASM_CLIENT_STATE_TYPE_URL => {
                decode_client_state(raw.value.deref()).map_err(Into::into)
            }
            _ => Err(Ics02Error::unexpected_client_state_type(
                WASM_CLIENT_STATE_TYPE_URL.to_string(),
                raw.type_url,
            )),
        }
    }
}

impl From<ClientState> for Any {
    fn from(client_state: ClientState) -> Self {
        Any {
            type_url: WASM_CLIENT_STATE_TYPE_URL.to_string(),
            value: Protobuf::<RawClientState>::encode_vec(client_state),
        }
    }
}
