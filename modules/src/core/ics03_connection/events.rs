//! Types for the IBC events emitted from Tendermint Websocket by the connection module.

use serde_derive::{Deserialize, Serialize};
use tendermint::abci::tag::Tag;
use tendermint::abci::Event as AbciEvent;

use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics02_client::height::Height;
use crate::core::ics03_connection::error::Error;
use crate::core::ics24_host::identifier::{ClientId, ConnectionId};
use crate::events::{IbcEvent, IbcEventType};
use crate::prelude::*;

/// The content of the `key` field for the attribute containing the connection identifier.
const HEIGHT_ATTRIBUTE_KEY: &str = "height";
const CONN_ID_ATTRIBUTE_KEY: &str = "connection_id";
const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";
const COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY: &str = "counterparty_connection_id";
const COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY: &str = "counterparty_client_id";

pub fn try_from_tx(event: &tendermint::abci::Event) -> Option<IbcEvent> {
    match event.type_str.parse() {
        Ok(IbcEventType::OpenInitConnection) => extract_attributes_from_tx(event)
            .map(OpenInit::from)
            .map(IbcEvent::OpenInitConnection)
            .ok(),
        Ok(IbcEventType::OpenTryConnection) => extract_attributes_from_tx(event)
            .map(OpenTry::from)
            .map(IbcEvent::OpenTryConnection)
            .ok(),
        Ok(IbcEventType::OpenAckConnection) => extract_attributes_from_tx(event)
            .map(OpenAck::from)
            .map(IbcEvent::OpenAckConnection)
            .ok(),
        Ok(IbcEventType::OpenConfirmConnection) => extract_attributes_from_tx(event)
            .map(OpenConfirm::from)
            .map(IbcEvent::OpenConfirmConnection)
            .ok(),
        _ => None,
    }
}

fn extract_attributes_from_tx(event: &tendermint::abci::Event) -> Result<Attributes, Error> {
    let mut attr = Attributes::default();

    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        match key {
            HEIGHT_ATTRIBUTE_KEY => {
                attr.height = value.parse().map_err(|e| {
                    Error::ics02_client(Ics02Error::invalid_string_as_height(value.to_string(), e))
                })?;
            }
            CONN_ID_ATTRIBUTE_KEY => {
                attr.connection_id = value.parse().ok();
            }
            CLIENT_ID_ATTRIBUTE_KEY => {
                attr.client_id = value.parse().map_err(Error::invalid_identifier)?;
            }
            COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY => {
                attr.counterparty_connection_id = value.parse().ok();
            }
            COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY => {
                attr.counterparty_client_id = value.parse().map_err(Error::invalid_identifier)?;
            }
            _ => {}
        }
    }

    Ok(attr)
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Attributes {
    pub height: Height,
    pub connection_id: Option<ConnectionId>,
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

/// Convert attributes to Tendermint ABCI tags
///
/// # Note
/// The parsing of `Key`s and `Value`s never fails, because the
/// `FromStr` instance of `tendermint::abci::tag::{Key, Value}`
/// is infallible, even if it is not represented in the error type.
/// Once tendermint-rs improves the API of the `Key` and `Value` types,
/// we will be able to remove the `.parse().unwrap()` calls.
impl From<Attributes> for Vec<Tag> {
    fn from(a: Attributes) -> Self {
        let mut attributes = vec![];
        let height = Tag {
            key: HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.height.to_string().parse().unwrap(),
        };
        attributes.push(height);
        if let Some(conn_id) = a.connection_id {
            let conn_id = Tag {
                key: CONN_ID_ATTRIBUTE_KEY.parse().unwrap(),
                value: conn_id.to_string().parse().unwrap(),
            };
            attributes.push(conn_id);
        }
        let client_id = Tag {
            key: CLIENT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.client_id.to_string().parse().unwrap(),
        };
        attributes.push(client_id);
        if let Some(conn_id) = a.counterparty_connection_id {
            let conn_id = Tag {
                key: COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY.parse().unwrap(),
                value: conn_id.to_string().parse().unwrap(),
            };
            attributes.push(conn_id);
        }
        let counterparty_client_id = Tag {
            key: COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.counterparty_client_id.to_string().parse().unwrap(),
        };
        attributes.push(counterparty_client_id);
        attributes
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct OpenInit(Attributes);

impl OpenInit {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn connection_id(&self) -> &Option<ConnectionId> {
        &self.0.connection_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
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

impl From<OpenInit> for AbciEvent {
    fn from(v: OpenInit) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::OpenInitConnection.as_str().to_string(),
            attributes,
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct OpenTry(Attributes);

impl OpenTry {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn connection_id(&self) -> &Option<ConnectionId> {
        &self.0.connection_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
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

impl From<OpenTry> for AbciEvent {
    fn from(v: OpenTry) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::OpenTryConnection.as_str().to_string(),
            attributes,
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct OpenAck(Attributes);

impl OpenAck {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn connection_id(&self) -> &Option<ConnectionId> {
        &self.0.connection_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
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

impl From<OpenAck> for AbciEvent {
    fn from(v: OpenAck) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::OpenAckConnection.as_str().to_string(),
            attributes,
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct OpenConfirm(Attributes);

impl OpenConfirm {
    pub fn attributes(&self) -> &Attributes {
        &self.0
    }
    pub fn connection_id(&self) -> &Option<ConnectionId> {
        &self.0.connection_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
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

impl From<OpenConfirm> for AbciEvent {
    fn from(v: OpenConfirm) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::OpenConfirmConnection.as_str().to_string(),
            attributes,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn connection_event_to_abci_event() {
        let height = Height::new(1, 1);
        let attributes = Attributes {
            height,
            connection_id: Some("test_connection".parse().unwrap()),
            client_id: "test_client".parse().unwrap(),
            counterparty_connection_id: Some("counterparty_test_conn".parse().unwrap()),
            counterparty_client_id: "counterparty_test_client".parse().unwrap(),
        };
        let mut abci_events = vec![];
        let open_init = OpenInit::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_init.clone()));
        let open_try = OpenTry::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_try.clone()));
        let open_ack = OpenAck::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_ack.clone()));
        let open_confirm = OpenConfirm::from(attributes);
        abci_events.push(AbciEvent::from(open_confirm.clone()));

        for event in abci_events {
            match try_from_tx(&event) {
                Some(e) => match e {
                    IbcEvent::OpenInitConnection(e) => assert_eq!(e.0, open_init.0),
                    IbcEvent::OpenTryConnection(e) => assert_eq!(e.0, open_try.0),
                    IbcEvent::OpenAckConnection(e) => assert_eq!(e.0, open_ack.0),
                    IbcEvent::OpenConfirmConnection(e) => assert_eq!(e.0, open_confirm.0),
                    _ => panic!("unexpected event type"),
                },
                None => panic!("converted event was wrong"),
            }
        }
    }
}
