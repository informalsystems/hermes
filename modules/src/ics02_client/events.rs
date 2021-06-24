//! Types for the IBC events emitted from Tendermint Websocket by the client module.
use std::convert::{TryFrom, TryInto};

use prost::Message;
use serde_derive::{Deserialize, Serialize};
use subtle_encoding::hex;
use tendermint_proto::Protobuf;

use crate::events::{self, extract_attribute, IbcEvent, RawObject};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::header::AnyHeader;
use crate::ics02_client::height::Height;
use crate::ics24_host::identifier::ClientId;

/// The content of the `type` field for the event that a chain produces upon executing the create client transaction.
const CREATE_EVENT_TYPE: &str = "create_client";
const UPDATE_EVENT_TYPE: &str = "update_client";
const MISBEHAVIOUR_EVENT_TYPE: &str = "client_misbehaviour";
const UPGRADE_EVENT_TYPE: &str = "upgrade_client";

/// The content of the `key` field for the attribute containing the client identifier.
const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";

/// The content of the `key` field for the attribute containing the client type.
const CLIENT_TYPE_ATTRIBUTE_KEY: &str = "client_type";

/// The content of the `key` field for the attribute containing the height.
const CONSENSUS_HEIGHT_ATTRIBUTE_KEY: &str = "consensus_height";

/// The content of the `key` field for the header in update client event.
const HEADER: &str = "header";

pub fn try_from_tx(event: &tendermint::abci::Event) -> Option<IbcEvent> {
    match event.type_str.as_ref() {
        CREATE_EVENT_TYPE => Some(IbcEvent::CreateClient(CreateClient(
            extract_attributes_from_tx(event),
        ))),
        UPDATE_EVENT_TYPE => Some(IbcEvent::UpdateClient(UpdateClient {
            common: extract_attributes_from_tx(event),
            header: extract_header_from_tx(event),
        })),
        MISBEHAVIOUR_EVENT_TYPE => Some(IbcEvent::ClientMisbehaviour(ClientMisbehaviour(
            extract_attributes_from_tx(event),
        ))),
        UPGRADE_EVENT_TYPE => Some(IbcEvent::UpgradeClient(UpgradeClient(
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

pub fn extract_header_from_tx(event: &tendermint::abci::Event) -> Option<AnyHeader> {
    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        if let HEADER = key {
            let header_bytes = hex::decode(value).unwrap();
            let header: AnyHeader = Protobuf::decode(header_bytes.as_ref()).unwrap();
            return Some(header);
        }
    }
    None
}

/// NewBlock event signals the committing & execution of a new block.
// TODO - find a better place for NewBlock
#[derive(Debug, Deserialize, Serialize, Clone, Copy)]
pub struct NewBlock {
    pub height: Height,
}

impl NewBlock {
    pub fn new(h: Height) -> NewBlock {
        NewBlock { height: h }
    }
    pub fn set_height(&mut self, height: Height) {
        self.height = height;
    }
    pub fn height(&self) -> Height {
        self.height
    }
}

impl From<NewBlock> for IbcEvent {
    fn from(v: NewBlock) -> Self {
        IbcEvent::NewBlock(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Attributes {
    pub height: Height,
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

impl std::fmt::Display for Attributes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "h: {}, cs_h: {}({})",
            self.height, self.client_id, self.consensus_height
        )
    }
}

fn extract_attributes(object: &RawObject, namespace: &str) -> Result<Attributes, events::Error> {
    Ok(Attributes {
        height: object.height,

        client_id: extract_attribute(object, &format!("{}.client_id", namespace))?
            .parse()
            .map_err(events::parse_error)?,

        client_type: extract_attribute(object, &format!("{}.client_type", namespace))?
            .parse()
            .map_err(events::client_error)?,

        consensus_height: extract_attribute(object, &format!("{}.consensus_height", namespace))?
            .as_str()
            .try_into()
            .map_err(events::height_error)?,
    })
}

/// CreateClient event signals the creation of a new on-chain client (IBC client).
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct CreateClient(Attributes);

impl CreateClient {
    pub fn client_id(&self) -> &ClientId {
        &self.0.client_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
}

impl From<Attributes> for CreateClient {
    fn from(attrs: Attributes) -> Self {
        CreateClient(attrs)
    }
}

impl TryFrom<RawObject> for CreateClient {
    type Error = events::Error;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        Ok(CreateClient(extract_attributes(&obj, "create_client")?))
    }
}

impl From<CreateClient> for IbcEvent {
    fn from(v: CreateClient) -> Self {
        IbcEvent::CreateClient(v)
    }
}

impl std::fmt::Display for CreateClient {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

/// UpdateClient event signals a recent update of an on-chain client (IBC Client).
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct UpdateClient {
    pub common: Attributes,
    pub header: Option<AnyHeader>,
}

impl UpdateClient {
    pub fn client_id(&self) -> &ClientId {
        &self.common.client_id
    }
    pub fn client_type(&self) -> ClientType {
        self.common.client_type
    }

    pub fn height(&self) -> Height {
        self.common.height
    }

    pub fn set_height(&mut self, height: Height) {
        self.common.height = height;
    }

    pub fn consensus_height(&self) -> Height {
        self.common.consensus_height
    }
}

impl From<Attributes> for UpdateClient {
    fn from(attrs: Attributes) -> Self {
        UpdateClient {
            common: attrs,
            header: None,
        }
    }
}

impl TryFrom<RawObject> for UpdateClient {
    type Error = events::Error;

    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        let header_str: Option<String> = obj
            .events
            .get("update_client.header")
            .and_then(|tags| tags[obj.idx].parse().ok());
        // some_attribute!(obj, "update_client.header");

        let header: Option<AnyHeader> = match header_str {
            Some(str) => {
                let header_bytes = hex::decode(str).map_err(events::subtle_encoding_error)?;

                let decoded = prost_types::Any::decode(header_bytes.as_ref())
                    .map_err(events::decode_error)?
                    .try_into()
                    .map_err(events::client_error)?;

                Some(decoded)
            }
            None => None,
        };

        Ok(UpdateClient {
            common: extract_attributes(&obj, "update_client")?,
            header,
        })
    }
}

impl From<UpdateClient> for IbcEvent {
    fn from(v: UpdateClient) -> Self {
        IbcEvent::UpdateClient(v)
    }
}

impl std::fmt::Display for UpdateClient {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.common)
    }
}

/// ClientMisbehaviour event signals the update of an on-chain client (IBC Client) with evidence of
/// misbehaviour.
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ClientMisbehaviour(Attributes);

impl ClientMisbehaviour {
    pub fn client_id(&self) -> &ClientId {
        &self.0.client_id
    }
    pub fn height(&self) -> Height {
        self.0.height
    }
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
}

impl TryFrom<RawObject> for ClientMisbehaviour {
    type Error = events::Error;
    fn try_from(obj: RawObject) -> Result<Self, Self::Error> {
        // attribute!(obj, "client_misbehaviour.consensus_height");
        Ok(ClientMisbehaviour(extract_attributes(
            &obj,
            "client_misbehaviour",
        )?))
    }
}

impl From<ClientMisbehaviour> for IbcEvent {
    fn from(v: ClientMisbehaviour) -> Self {
        IbcEvent::ClientMisbehaviour(v)
    }
}

/// Signals a recent upgrade of an on-chain client (IBC Client).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct UpgradeClient(Attributes);

impl UpgradeClient {
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
    pub fn client_id(&self) -> &ClientId {
        &self.0.client_id
    }
}

impl From<Attributes> for UpgradeClient {
    fn from(attrs: Attributes) -> Self {
        UpgradeClient(attrs)
    }
}
