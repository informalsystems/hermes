//! Types for the IBC events emitted from Tendermint Websocket by the client module.
use crate::attribute;
use crate::events::{IBCEvent, RawObject};
use crate::ics02_client::client_type::ClientType;
use crate::ics24_host::identifier::ClientId;
use anomaly::BoxError;

use crate::ics02_client::height::Height;
use serde_derive::{Deserialize, Serialize};
use std::collections::HashSet;
use std::convert::{TryFrom, TryInto};
use std::iter::FromIterator;
use tendermint::block;

/// The content of the `type` field for the event that a chain produces upon executing the create client transaction.
pub const CREATE_EVENT_TYPE: &str = "create_client";
pub const UPDATE_EVENT_TYPE: &str = "update_client";

/// The content of the `key` field for the attribute containing the client identifier.
pub const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";

/// The content of the `key` field for the attribute containing the client type.
pub const CLIENT_TYPE_ATTRIBUTE_KEY: &str = "client_type";

/// The content of the `key` field for the attribute containing the height.
pub const CONSENSUS_HEIGHT_ATTRIBUTE_KEY: &str = "consensus_height";

/// A list of all the event `type`s that this module is capable of parsing
fn event_types() -> HashSet<String> {
    HashSet::from_iter(
        vec![CREATE_EVENT_TYPE.to_string(), UPDATE_EVENT_TYPE.to_string()]
            .iter()
            .cloned(),
    )
}

pub fn try_from_tx(event: tendermint::abci::Event) -> Option<IBCEvent> {
    event_types().get(&event.type_str)?;
    let mut attr = Attributes::default();

    for tag in event.attributes {
        match tag.key.as_ref() {
            CLIENT_ID_ATTRIBUTE_KEY => attr.client_id = tag.value.to_string().parse().unwrap(),
            CLIENT_TYPE_ATTRIBUTE_KEY => attr.client_type = tag.value.to_string().parse().unwrap(),
            CONSENSUS_HEIGHT_ATTRIBUTE_KEY => {
                attr.consensus_height = tag.value.to_string().try_into().unwrap()
            }
            _ => {}
        }
    }

    match event.type_str.as_str() {
        CREATE_EVENT_TYPE => Some(IBCEvent::CreateClient(CreateClient(attr))),
        UPDATE_EVENT_TYPE => Some(IBCEvent::UpdateClient(UpdateClient(attr))),
        _ => None,
    }
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

impl TryFrom<RawObject> for CreateClient {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let consensus_height_str: String = attribute!(obj, "create_client.consensus_height");
        Ok(CreateClient(Attributes {
            height: obj.height,
            client_id: attribute!(obj, "create_client.client_id"),
            client_type: attribute!(obj, "create_client.client_type"),
            consensus_height: consensus_height_str.try_into()?,
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

impl TryFrom<RawObject> for UpdateClient {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let consensus_height_str: String = attribute!(obj, "update_client.consensus_height");
        Ok(UpdateClient(Attributes {
            height: obj.height,
            client_id: attribute!(obj, "update_client.client_id"),
            client_type: attribute!(obj, "update_client.client_type"),
            consensus_height: consensus_height_str.try_into()?,
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
            consensus_height: consensus_height_str.try_into()?,
        }))
    }
}

impl From<ClientMisbehavior> for IBCEvent {
    fn from(v: ClientMisbehavior) -> Self {
        IBCEvent::ClientMisbehavior(v)
    }
}
