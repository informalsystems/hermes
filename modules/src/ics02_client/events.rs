//! Types for the IBC events emitted from Tendermint Websocket by the client module.
use crate::attribute;
use crate::events::{IBCEvent, RawObject};
use crate::ics02_client::client_type::ClientType;
use crate::ics24_host::identifier::ClientId;
use anomaly::BoxError;

use crate::ics02_client::height::Height;
use serde_derive::{Deserialize, Serialize};
use std::convert::{TryFrom, TryInto};
use tendermint::block;

/// The content of the `type` field for the event that a chain produces upon executing the create client transaction.
const CREATE_EVENT_TYPE: &str = "create_client";
const UPDATE_EVENT_TYPE: &str = "update_client";

/// The content of the `key` field for the attribute containing the client identifier.
const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";

/// The content of the `key` field for the attribute containing the client type.
const CLIENT_TYPE_ATTRIBUTE_KEY: &str = "client_type";

/// The content of the `key` field for the attribute containing the height.
const CONSENSUS_HEIGHT_ATTRIBUTE_KEY: &str = "consensus_height";

pub fn try_from_tx(event: &tendermint::abci::Event) -> Option<IBCEvent> {
    match event.type_str.as_ref() {
        CREATE_EVENT_TYPE => Some(IBCEvent::CreateClient(CreateClient(
            extract_attributes_from_tx(event),
        ))),
        UPDATE_EVENT_TYPE => Some(IBCEvent::UpdateClient(UpdateClient(
            extract_attributes_from_tx(event),
        ))),
        _ => None,
    }
}

fn extract_attributes_from_tx(event: &tendermint::abci::Event) -> Attributes {
    let mut attr = Attributes::default();

    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        match key {
            CLIENT_ID_ATTRIBUTE_KEY => attr.client_id = value.parse().unwrap(),
            CLIENT_TYPE_ATTRIBUTE_KEY => attr.client_type = value.parse().unwrap(),
            CONSENSUS_HEIGHT_ATTRIBUTE_KEY => attr.consensus_height = value.parse().unwrap(),
            // TODO: `Attributes` has 4 fields and we're only parsing 3
            _ => {}
        }
    }

    attr
}

/// NewBlock event signals the committing & execution of a new block.
// TODO - find a better place for NewBlock
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct NewBlock {
    pub height: block::Height,
}

impl NewBlock {
    pub fn new(h: block::Height) -> NewBlock {
        NewBlock { height: h }
    }
}

impl From<NewBlock> for IBCEvent {
    fn from(v: NewBlock) -> Self {
        IBCEvent::NewBlock(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct Attributes {
    pub height: block::Height,
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub consensus_height: Height,
}

impl Default for Attributes {
    fn default() -> Self {
        Attributes {
            height: Default::default(),
            client_id: Default::default(),
            client_type: ClientType::Tendermint,
            consensus_height: Height::default(),
        }
    }
}

/// CreateClient event signals the creation of a new on-chain client (IBC client).
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct CreateClient(Attributes);

impl CreateClient {
    pub fn client_id(&self) -> &ClientId {
        &self.0.client_id
    }
}

impl From<Attributes> for CreateClient {
    fn from(attrs: Attributes) -> Self {
        CreateClient(attrs)
    }
}

impl TryFrom<RawObject> for CreateClient {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let consensus_height_str: String = attribute!(obj, "create_client.consensus_height");
        Ok(CreateClient(Attributes {
            height: obj.height,
            client_id: attribute!(obj, "create_client.client_id"),
            client_type: attribute!(obj, "create_client.client_type"),
            consensus_height: consensus_height_str.as_str().try_into()?,
        }))
    }
}

impl From<CreateClient> for IBCEvent {
    fn from(v: CreateClient) -> Self {
        IBCEvent::CreateClient(v)
    }
}

/// UpdateClient event signals a recent update of an on-chain client (IBC Client).
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct UpdateClient(Attributes);

impl UpdateClient {
    pub fn client_id(&self) -> &ClientId {
        &self.0.client_id
    }

    pub fn height(&self) -> &tendermint::block::Height {
        &self.0.height
    }
}

impl From<Attributes> for UpdateClient {
    fn from(attrs: Attributes) -> Self {
        UpdateClient(attrs)
    }
}

impl TryFrom<RawObject> for UpdateClient {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let consensus_height_str: String = attribute!(obj, "update_client.consensus_height");
        Ok(UpdateClient(Attributes {
            height: obj.height,
            client_id: attribute!(obj, "update_client.client_id"),
            client_type: attribute!(obj, "update_client.client_type"),
            consensus_height: consensus_height_str.as_str().try_into()?,
        }))
    }
}

impl From<UpdateClient> for IBCEvent {
    fn from(v: UpdateClient) -> Self {
        IBCEvent::UpdateClient(v)
    }
}

/// ClientMisbehavior event signals the update of an on-chain client (IBC Client) with evidence of
/// misbehavior.
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ClientMisbehavior(Attributes);

impl TryFrom<RawObject> for ClientMisbehavior {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let consensus_height_str: String = attribute!(obj, "client_misbehaviour.consensus_height");
        Ok(ClientMisbehavior(Attributes {
            height: obj.height,
            client_id: attribute!(obj, "client_misbehaviour.client_id"),
            client_type: attribute!(obj, "client_misbehaviour.client_type"),
            consensus_height: consensus_height_str.as_str().try_into()?,
        }))
    }
}

impl From<ClientMisbehavior> for IBCEvent {
    fn from(v: ClientMisbehavior) -> Self {
        IBCEvent::ClientMisbehavior(v)
    }
}
