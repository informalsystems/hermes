//! Types for the IBC events emitted from Tendermint Websocket by the client module.
use crate::attribute;
use crate::events::{IBCEvent, RawObject};
use crate::ics02_client::client_type::ClientType;
use crate::ics24_host::identifier::ClientId;
use anomaly::BoxError;

use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::block;

/// The content of the `type` field for the event that a chain produces upon executing the create client transaction.
pub const CREATE_EVENT_TYPE: &str = "create_client";

/// The content of the `key` field for the attribute containing the client identifier.
pub const CREATE_ID_ATTRIBUTE_KEY: &str = "client_id";

/// The content of the `key` field for the attribute containing the client type.
pub const CREATE_TYPE_ATTRIBUTE_KEY: &str = "client_type";

/// The content of the `key` field for the attribute containing the height.
pub const CREATE_HEIGHT_ATTRIBUTE_KEY: &str = "consensus_height";

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

/// CreateClient event signals the creation of a new on-chain client (IBC client).
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct CreateClient {
    pub height: block::Height,
    pub client_id: ClientId,
    pub client_type: ClientType,
}

impl TryFrom<RawObject> for CreateClient {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(CreateClient {
            height: obj.height,
            client_id: attribute!(obj, "create_client.client_id"),
            client_type: attribute!(obj, "create_client.client_type"),
        })
    }
}

impl From<CreateClient> for IBCEvent {
    fn from(v: CreateClient) -> Self {
        IBCEvent::CreateClient(v)
    }
}

/// UpdateClient event signals a recent update of an on-chain client (IBC Client).
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct UpdateClient {
    pub height: block::Height,
    pub client_id: ClientId,
    pub client_type: ClientType,
}

impl TryFrom<RawObject> for UpdateClient {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(UpdateClient {
            height: obj.height,
            client_id: attribute!(obj, "update_client.client_id"),
            client_type: attribute!(obj, "update_client.client_type"),
        })
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
pub struct ClientMisbehavior {
    pub height: block::Height,
    pub client_id: ClientId,
    pub client_type: ClientType,
}

impl TryFrom<RawObject> for ClientMisbehavior {
    type Error = BoxError;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(ClientMisbehavior {
            height: obj.height,
            client_id: attribute!(obj, "client_misbehaviour.client_id"),
            client_type: attribute!(obj, "client_misbehaviour.client_type"),
        })
    }
}

impl From<ClientMisbehavior> for IBCEvent {
    fn from(v: ClientMisbehavior) -> Self {
        IBCEvent::ClientMisbehavior(v)
    }
}
