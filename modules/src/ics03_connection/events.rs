//! Types for the IBC events emitted from Tendermint Websocket by the connection module.
use crate::events::{IBCEvent, RawObject};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::{attribute, some_attribute};
use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::block;

/// The content of the `type` field for the event that a chain produces upon executing a connection handshake transaction.
pub const INIT_EVENT_TYPE: &str = "connection_open_init";
pub const TRY_EVENT_TYPE: &str = "connection_open_try";
pub const ACK_EVENT_TYPE: &str = "connection_open_ack";
pub const CONFIRM_EVENT_TYPE: &str = "connection_open_confirm";

/// The content of the `key` field for the attribute containing the connection identifier.
const CONN_ID_ATTRIBUTE_KEY: &str = "connection_id";
const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";
const COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY: &str = "counterparty_connection_id";
const COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY: &str = "counterparty_client_id";

pub fn try_from_event(event: &crate::events::GenericEvent<'_>) -> Option<IBCEvent> {
    match event.type_str {
        INIT_EVENT_TYPE => Some(IBCEvent::OpenInitConnection(OpenInit::from(
            extract_attributes_from_event(event),
        ))),
        TRY_EVENT_TYPE => Some(IBCEvent::OpenTryConnection(OpenTry::from(
            extract_attributes_from_event(event),
        ))),
        ACK_EVENT_TYPE => Some(IBCEvent::OpenAckConnection(OpenAck::from(
            extract_attributes_from_event(event),
        ))),
        CONFIRM_EVENT_TYPE => Some(IBCEvent::OpenConfirmConnection(OpenConfirm::from(
            extract_attributes_from_event(event),
        ))),
        _ => None,
    }
}

fn extract_attributes_from_event(event: &crate::events::GenericEvent<'_>) -> Attributes {
    let mut attr = Attributes::default();

    for (key, value) in &event.attributes {
        match *key {
            CONN_ID_ATTRIBUTE_KEY => attr.connection_id = value.parse().unwrap(),
            CLIENT_ID_ATTRIBUTE_KEY => attr.client_id = value.parse().unwrap(),
            COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY => {
                attr.counterparty_connection_id = value.parse().ok()
            }
            COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY => {
                attr.counterparty_client_id = value.parse().unwrap()
            }
            // TODO: `Attributes` has 5 fields and we're only parsing 4; is that intended?
            _ => panic!("unexpected attribute key: {}", key),
        }
    }

    attr
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct Attributes {
    pub height: block::Height,
    pub connection_id: ConnectionId,
    pub client_id: ClientId,
    pub counterparty_connection_id: Option<ConnectionId>,
    pub counterparty_client_id: ClientId,
}

impl Default for Attributes {
    fn default() -> Self {
        Attributes {
            height: Default::default(),
            connection_id: Default::default(),
            client_id: Default::default(),
            counterparty_connection_id: Default::default(),
            counterparty_client_id: Default::default(),
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenInit(Attributes);

impl OpenInit {
    pub fn connection_id(&self) -> &ConnectionId {
        &self.0.connection_id
    }
}

impl From<Attributes> for OpenInit {
    fn from(attrs: Attributes) -> Self {
        OpenInit(attrs)
    }
}

impl TryFrom<RawObject> for OpenInit {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenInit(Attributes {
            height: obj.height,
            connection_id: attribute!(obj, "connection_open_init.connection_id"),
            client_id: attribute!(obj, "connection_open_init.client_id"),
            counterparty_connection_id: some_attribute!(
                obj,
                "connection_open_init.counterparty_connection_id"
            ),
            counterparty_client_id: attribute!(obj, "connection_open_init.counterparty_client_id"),
        }))
    }
}

impl From<OpenInit> for IBCEvent {
    fn from(v: OpenInit) -> Self {
        IBCEvent::OpenInitConnection(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenTry(Attributes);

impl OpenTry {
    pub fn connection_id(&self) -> &ConnectionId {
        &self.0.connection_id
    }
}

impl From<Attributes> for OpenTry {
    fn from(attrs: Attributes) -> Self {
        OpenTry(attrs)
    }
}

impl TryFrom<RawObject> for OpenTry {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenTry(Attributes {
            height: obj.height,
            connection_id: attribute!(obj, "connection_open_try.connection_id"),
            client_id: attribute!(obj, "connection_open_try.client_id"),
            counterparty_connection_id: some_attribute!(
                obj,
                "connection_open_try.counterparty_connection_id"
            ),
            counterparty_client_id: attribute!(obj, "connection_open_try.counterparty_client_id"),
        }))
    }
}

impl From<OpenTry> for IBCEvent {
    fn from(v: OpenTry) -> Self {
        IBCEvent::OpenTryConnection(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenAck(Attributes);

impl OpenAck {
    pub fn connection_id(&self) -> &ConnectionId {
        &self.0.connection_id
    }
}

impl From<Attributes> for OpenAck {
    fn from(attrs: Attributes) -> Self {
        OpenAck(attrs)
    }
}

impl TryFrom<RawObject> for OpenAck {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenAck(Attributes {
            height: obj.height,
            connection_id: attribute!(obj, "connection_open_ack.connection_id"),
            client_id: attribute!(obj, "connection_open_ack.client_id"),
            counterparty_connection_id: some_attribute!(
                obj,
                "connection_open_ack.counterparty_connection_id"
            ),
            counterparty_client_id: attribute!(obj, "connection_open_ack.counterparty_client_id"),
        }))
    }
}

impl From<OpenAck> for IBCEvent {
    fn from(v: OpenAck) -> Self {
        IBCEvent::OpenAckConnection(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenConfirm(Attributes);

impl OpenConfirm {
    pub fn connection_id(&self) -> &ConnectionId {
        &self.0.connection_id
    }
}

impl From<Attributes> for OpenConfirm {
    fn from(attrs: Attributes) -> Self {
        OpenConfirm(attrs)
    }
}

impl TryFrom<RawObject> for OpenConfirm {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenConfirm(Attributes {
            height: obj.height,
            connection_id: attribute!(obj, "connection_open_confirm.connection_id"),
            client_id: attribute!(obj, "connection_open_confirm.client_id"),
            counterparty_connection_id: some_attribute!(
                obj,
                "connection_open_confirm.counterparty_connection_id"
            ),
            counterparty_client_id: attribute!(
                obj,
                "connection_open_confirm.counterparty_client_id"
            ),
        }))
    }
}

impl From<OpenConfirm> for IBCEvent {
    fn from(v: OpenConfirm) -> Self {
        IBCEvent::OpenConfirmConnection(v)
    }
}
