use crate::attribute;
use crate::events::{IBCEvent, TryObject};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::block;

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenInit {
    pub height: block::Height,
    pub connection_id: ConnectionId,
    pub client_id: ClientId,
    pub counterparty_client_id: ClientId,
}

impl TryFrom<TryObject> for OpenInit {
    type Error = Box<dyn std::error::Error>;
    fn try_from(obj: TryObject) -> Result<Self, Self::Error> {
        Ok(OpenInit {
            height: obj.height,
            connection_id: attribute!(obj, "connection_open_init.connection_id"),
            client_id: attribute!(obj, "connection_open_init.counterparty_client_id"),
            counterparty_client_id: attribute!(obj, "connection_open_init.client_id"),
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
    pub height: block::Height,
    pub connection_id: ConnectionId,
    pub client_id: ClientId,
    pub counterparty_client_id: ClientId,
}

impl TryFrom<TryObject> for OpenTry {
    type Error = Box<dyn std::error::Error>;
    fn try_from(obj: TryObject) -> Result<Self, Self::Error> {
        Ok(OpenTry {
            height: obj.height,
            connection_id: attribute!(obj, "connection_open_try.connection_id"),
            client_id: attribute!(obj, "connection_open_try.counterparty_client_id"),
            counterparty_client_id: attribute!(obj, "connection_open_try.client_id"),
        })
    }
}

impl From<OpenTry> for IBCEvent {
    fn from(v: OpenTry) -> Self {
        IBCEvent::OpenTryConnection(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenAck {
    pub height: block::Height,
    pub connection_id: ConnectionId,
}

impl TryFrom<TryObject> for OpenAck {
    type Error = Box<dyn std::error::Error>;
    fn try_from(obj: TryObject) -> Result<Self, Self::Error> {
        Ok(OpenAck {
            height: obj.height,
            connection_id: attribute!(obj, "connection_open_ack.connection_id"),
        })
    }
}

impl From<OpenAck> for IBCEvent {
    fn from(v: OpenAck) -> Self {
        IBCEvent::OpenAckConnection(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenConfirm {
    pub height: block::Height,
    pub connection_id: ConnectionId,
}

impl TryFrom<TryObject> for OpenConfirm {
    type Error = Box<dyn std::error::Error>;
    fn try_from(obj: TryObject) -> Result<Self, Self::Error> {
        Ok(OpenConfirm {
            height: obj.height,
            connection_id: attribute!(obj, "connection_open_confirm.connection_id"),
        })
    }
}

impl From<OpenConfirm> for IBCEvent {
    fn from(v: OpenConfirm) -> Self {
        IBCEvent::OpenConfirmConnection(v)
    }
}
