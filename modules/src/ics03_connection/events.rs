//! Types for the IBC events emitted from Tendermint Websocket by the connection module.
use crate::attribute;
use crate::events::{IBCEvent, RawObject};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::block;

use std::collections::HashSet;
use std::iter::FromIterator;

/// The content of the `type` field for the event that a chain produces upon executing a connection handshake transaction.
const INIT_EVENT_TYPE: &str = "connection_open_init";
const TRY_EVENT_TYPE: &str = "connection_open_try";
const ACK_EVENT_TYPE: &str = "connection_open_ack";
const CONFIRM_EVENT_TYPE: &str = "connection_open_confirm";

/// The content of the `key` field for the attribute containing the connection identifier.
pub const CONN_ID_ATTRIBUTE_KEY: &str = "connection_id";

/// A list of all the event `type`s that this module is capable of parsing
fn event_types() -> HashSet<String> {
    HashSet::from_iter(
        vec![
            INIT_EVENT_TYPE.to_string(),
            TRY_EVENT_TYPE.to_string(),
            ACK_EVENT_TYPE.to_string(),
            CONFIRM_EVENT_TYPE.to_string(),
        ]
        .iter()
        .cloned(),
    )
}

pub fn try_from_tx(event: tendermint::abci::Event) -> Option<IBCEvent> {
    event_types().get(&event.type_str)?; // Quit fast if the event type is irrelevant
    let mut attr = Attributes::default();

    for tag in event.attributes {
        if CONN_ID_ATTRIBUTE_KEY == tag.key.as_ref() {
            attr.connection_id = tag.value.to_string().parse().unwrap()
        }
    }

    match event.type_str.as_str() {
        INIT_EVENT_TYPE => Some(IBCEvent::OpenInitConnection(OpenInit::from(attr))),
        _ => None,
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct Attributes {
    pub height: block::Height,
    pub connection_id: ConnectionId,
}

impl Default for Attributes {
    fn default() -> Self {
        Attributes {
            height: Default::default(),
            connection_id: Default::default(),
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenInit {
    pub common_attributes: Attributes,
    pub client_id: ClientId,
    pub counterparty_client_id: ClientId,
}

impl From<Attributes> for OpenInit {
    fn from(attrs: Attributes) -> Self {
        OpenInit {
            common_attributes: attrs,
            client_id: Default::default(),
            counterparty_client_id: Default::default(),
        }
    }
}

impl TryFrom<RawObject> for OpenInit {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenInit {
            common_attributes: Attributes {
                height: obj.height,
                connection_id: attribute!(obj, "connection_open_init.connection_id"),
            },
            client_id: attribute!(obj, "connection_open_init.client_id"),
            counterparty_client_id: attribute!(obj, "connection_open_init.counterparty_client_id"),
        })
    }
}

impl From<OpenInit> for IBCEvent {
    fn from(v: OpenInit) -> Self {
        IBCEvent::OpenInitConnection(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenTry {
    pub common_attributes: Attributes,
    pub client_id: ClientId,
    pub counterparty_client_id: ClientId,
}

impl From<Attributes> for OpenTry {
    fn from(attrs: Attributes) -> Self {
        OpenTry {
            common_attributes: attrs,
            client_id: Default::default(),
            counterparty_client_id: Default::default(),
        }
    }
}

impl TryFrom<RawObject> for OpenTry {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(OpenTry {
            common_attributes: Attributes {
                height: obj.height,
                connection_id: attribute!(obj, "connection_open_try.connection_id"),
            },
            client_id: attribute!(obj, "connection_open_try.client_id"),
            counterparty_client_id: attribute!(obj, "connection_open_try.counterparty_client_id"),
        })
    }
}

impl From<OpenTry> for IBCEvent {
    fn from(v: OpenTry) -> Self {
        IBCEvent::OpenTryConnection(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenAck(Attributes);

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
        }))
    }
}

impl From<OpenConfirm> for IBCEvent {
    fn from(v: OpenConfirm) -> Self {
        IBCEvent::OpenConfirmConnection(v)
    }
}
