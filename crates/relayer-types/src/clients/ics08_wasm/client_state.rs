//! Defines the client state type for the ICS-08 Wasm light client.

use std::time::Duration;

use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};

use crate::core::ics02_client::client_state::ClientState as Ics02ClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics02_client::height::Height;
use crate::core::ics24_host::identifier::ChainId;

use super::error::Error;
use super::proto::v1::ClientState as RawClientState;

pub const WASM_CLIENT_STATE_TYPE_URL: &str = "/ibc.lightclients.wasm.v1.ClientState";

/// The Wasm client state tracks the location of the Wasm bytecode via codeHash.
/// Binary data represented by the data field is opaque and only interpreted by the Wasm contract.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ClientState {
    pub data: Vec<u8>,
    pub checksum: Vec<u8>,
    pub latest_height: Height,
}

impl Ics02ClientState for ClientState {
    fn chain_id(&self) -> ChainId {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn latest_height(&self) -> Height {
        todo!()
    }

    fn frozen_height(&self) -> Option<Height> {
        todo!()
    }

    fn expired(&self, _elapsed: Duration) -> bool {
        todo!()
    }
}

impl Protobuf<RawClientState> for ClientState {}

impl From<ClientState> for RawClientState {
    fn from(value: ClientState) -> Self {
        RawClientState {
            data: value.data,
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
            data: value.data,
            checksum: value.checksum,
            latest_height: raw_height
                .clone()
                .try_into()
                .map_err(|_| Error::invalid_raw_height(raw_height))?,
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
            RawClientState::decode(buf)
                .map_err(Error::decode)?
                .try_into()
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
