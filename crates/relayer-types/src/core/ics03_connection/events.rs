//! Types for the IBC events emitted from Tendermint Websocket by the connection module.

use core::fmt::{Display, Error as FmtError, Formatter};
use serde_derive::{Deserialize, Serialize};
use tendermint::abci;

use crate::core::ics24_host::identifier::{ClientId, ConnectionId};
use crate::events::{IbcEvent, IbcEventType};
use crate::prelude::*;

/// The content of the `key` field for the attribute containing the connection identifier.
pub const CONN_ID_ATTRIBUTE_KEY: &str = "connection_id";
pub const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";
pub const COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY: &str = "counterparty_connection_id";
pub const COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY: &str = "counterparty_client_id";

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Attributes {
    pub connection_id: Option<ConnectionId>,
    pub client_id: ClientId,
    pub counterparty_connection_id: Option<ConnectionId>,
    pub counterparty_client_id: ClientId,
}

impl Display for Attributes {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match (&self.connection_id, &self.counterparty_connection_id) {
            (Some(connection_id), Some(counterparty_connection_id)) => write!(f, "Attributes {{ connection_id: {}, client_id: {}, counterparty_connection_id: {}, counterparty_client_id: {} }}", connection_id, self.client_id, counterparty_connection_id, self.counterparty_client_id),
            (Some(connection_id), None) => write!(f, "Attributes {{ connection_id: {}, client_id: {}, counterparty_connection_id: None, counterparty_client_id: {} }}", connection_id, self.client_id, self.counterparty_client_id),
            (None, Some(counterparty_connection_id)) => write!(f, "Attributes {{ connection_id: None, client_id: {}, counterparty_connection_id: {}, counterparty_client_id: {} }}", self.client_id, counterparty_connection_id, self.counterparty_client_id),
            (None, None) => write!(f, "Attributes {{ connection_id: None, client_id: {}, counterparty_connection_id: None, counterparty_client_id: {} }}", self.client_id, self.counterparty_client_id),
        }
    }
}

/// Convert attributes to Tendermint ABCI tags
impl From<Attributes> for Vec<abci::EventAttribute> {
    fn from(a: Attributes) -> Self {
        let mut attributes = vec![];
        if let Some(conn_id) = a.connection_id {
            let conn_id = (CONN_ID_ATTRIBUTE_KEY, conn_id.as_str()).into();
            attributes.push(conn_id);
        }
        let client_id = (CLIENT_ID_ATTRIBUTE_KEY, a.client_id.as_str()).into();
        attributes.push(client_id);
        if let Some(conn_id) = a.counterparty_connection_id {
            let conn_id = (COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY, conn_id.as_str()).into();
            attributes.push(conn_id);
        }
        let counterparty_client_id = (
            COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY,
            a.counterparty_client_id.to_string(),
        )
            .into();
        attributes.push(counterparty_client_id);
        attributes
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenInit(pub Attributes);

impl OpenInit {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn connection_id(&self) -> Option<&ConnectionId> {
        self.0.connection_id.as_ref()
    }
}

impl Display for OpenInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "OpenInit {{ {} }}", self.0)
    }
}

impl From<Attributes> for OpenInit {
    fn from(attrs: Attributes) -> Self {
        OpenInit(attrs)
    }
}

impl From<OpenInit> for IbcEvent {
    fn from(v: OpenInit) -> Self {
        IbcEvent::OpenInitConnection(v)
    }
}

impl From<OpenInit> for abci::Event {
    fn from(v: OpenInit) -> Self {
        Self {
            kind: IbcEventType::OpenInitConnection.as_str().to_owned(),
            attributes: v.0.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenTry(pub Attributes);

impl OpenTry {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn connection_id(&self) -> Option<&ConnectionId> {
        self.0.connection_id.as_ref()
    }
}

impl Display for OpenTry {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "OpenTry {{ {} }}", self.0)
    }
}

impl From<Attributes> for OpenTry {
    fn from(attrs: Attributes) -> Self {
        OpenTry(attrs)
    }
}

impl From<OpenTry> for IbcEvent {
    fn from(v: OpenTry) -> Self {
        IbcEvent::OpenTryConnection(v)
    }
}

impl From<OpenTry> for abci::Event {
    fn from(v: OpenTry) -> Self {
        Self {
            kind: IbcEventType::OpenTryConnection.as_str().to_owned(),
            attributes: v.0.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenAck(pub Attributes);

impl OpenAck {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn connection_id(&self) -> Option<&ConnectionId> {
        self.0.connection_id.as_ref()
    }
}

impl Display for OpenAck {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "OpenAck {{ {} }}", self.0)
    }
}

impl From<Attributes> for OpenAck {
    fn from(attrs: Attributes) -> Self {
        OpenAck(attrs)
    }
}

impl From<OpenAck> for IbcEvent {
    fn from(v: OpenAck) -> Self {
        IbcEvent::OpenAckConnection(v)
    }
}

impl From<OpenAck> for abci::Event {
    fn from(v: OpenAck) -> Self {
        Self {
            kind: IbcEventType::OpenAckConnection.as_str().to_owned(),
            attributes: v.0.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OpenConfirm(pub Attributes);

impl OpenConfirm {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn connection_id(&self) -> Option<&ConnectionId> {
        self.0.connection_id.as_ref()
    }
}

impl Display for OpenConfirm {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "OpenConfirm {{ {} }}", self.0)
    }
}

impl From<Attributes> for OpenConfirm {
    fn from(attrs: Attributes) -> Self {
        OpenConfirm(attrs)
    }
}

impl From<OpenConfirm> for IbcEvent {
    fn from(v: OpenConfirm) -> Self {
        IbcEvent::OpenConfirmConnection(v)
    }
}

impl From<OpenConfirm> for abci::Event {
    fn from(v: OpenConfirm) -> Self {
        Self {
            kind: IbcEventType::OpenConfirmConnection.as_str().to_owned(),
            attributes: v.0.into(),
        }
    }
}
