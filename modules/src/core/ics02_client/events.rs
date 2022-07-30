//! Types for the IBC events emitted from Tendermint Websocket by the client module.

use serde_derive::{Deserialize, Serialize};
use tendermint::abci::tag::Tag;
use tendermint::abci::Event as AbciEvent;

use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::header::AnyHeader;
use crate::core::ics02_client::height::Height;
use crate::core::ics24_host::identifier::ClientId;
use crate::events::{IbcEvent, IbcEventType};
use crate::prelude::*;

/// The content of the `key` field for the attribute containing the height.
pub const HEIGHT_ATTRIBUTE_KEY: &str = "height";

/// The content of the `key` field for the attribute containing the client identifier.
pub const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";

/// The content of the `key` field for the attribute containing the client type.
pub const CLIENT_TYPE_ATTRIBUTE_KEY: &str = "client_type";

/// The content of the `key` field for the attribute containing the height.
pub const CONSENSUS_HEIGHT_ATTRIBUTE_KEY: &str = "consensus_height";

/// The content of the `key` field for the header in update client event.
pub const HEADER_ATTRIBUTE_KEY: &str = "header";

/// NewBlock event signals the committing & execution of a new block.
// TODO - find a better place for NewBlock
#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
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
            height: Height::new(0, 1).unwrap(),
            client_id: Default::default(),
            client_type: ClientType::Tendermint,
            consensus_height: Height::new(0, 1).unwrap(),
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
        let height = Tag {
            key: HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.height.to_string().parse().unwrap(),
        };
        let client_id = Tag {
            key: CLIENT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.client_id.to_string().parse().unwrap(),
        };
        let client_type = Tag {
            key: CLIENT_TYPE_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.client_type.as_str().parse().unwrap(),
        };
        let consensus_height = Tag {
            key: CONSENSUS_HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.height.to_string().parse().unwrap(),
        };
        vec![height, client_id, client_type, consensus_height]
    }
}

impl core::fmt::Display for Attributes {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(
            f,
            "h: {}, cs_h: {}({})",
            self.height, self.client_id, self.consensus_height
        )
    }
}

/// CreateClient event signals the creation of a new on-chain client (IBC client).
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct CreateClient(pub Attributes);

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

impl From<CreateClient> for IbcEvent {
    fn from(v: CreateClient) -> Self {
        IbcEvent::CreateClient(v)
    }
}

impl From<CreateClient> for AbciEvent {
    fn from(v: CreateClient) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::CreateClient.as_str().to_string(),
            attributes,
        }
    }
}

impl core::fmt::Display for CreateClient {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

/// UpdateClient event signals a recent update of an on-chain client (IBC Client).
#[derive(Serialize, Clone, PartialEq, Eq)]
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

impl From<UpdateClient> for IbcEvent {
    fn from(v: UpdateClient) -> Self {
        IbcEvent::UpdateClient(v)
    }
}

impl From<UpdateClient> for AbciEvent {
    fn from(v: UpdateClient) -> Self {
        let mut attributes = Vec::<Tag>::from(v.common);
        if let Some(h) = v.header {
            let header = Tag {
                key: HEADER_ATTRIBUTE_KEY.parse().unwrap(),
                value: h.encode_to_string().parse().unwrap(),
            };
            attributes.push(header);
        }
        AbciEvent {
            type_str: IbcEventType::UpdateClient.as_str().to_string(),
            attributes,
        }
    }
}

impl core::fmt::Display for UpdateClient {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{}", self.common)
    }
}

impl core::fmt::Debug for UpdateClient {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.common)
    }
}

/// ClientMisbehaviour event signals the update of an on-chain client (IBC Client) with evidence of
/// misbehaviour.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct ClientMisbehaviour(pub Attributes);

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

impl From<Attributes> for ClientMisbehaviour {
    fn from(attrs: Attributes) -> Self {
        ClientMisbehaviour(attrs)
    }
}

impl From<ClientMisbehaviour> for IbcEvent {
    fn from(v: ClientMisbehaviour) -> Self {
        IbcEvent::ClientMisbehaviour(v)
    }
}

impl From<ClientMisbehaviour> for AbciEvent {
    fn from(v: ClientMisbehaviour) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::ClientMisbehaviour.as_str().to_string(),
            attributes,
        }
    }
}

/// Signals a recent upgrade of an on-chain client (IBC Client).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct UpgradeClient(pub Attributes);

impl UpgradeClient {
    pub fn set_height(&mut self, height: Height) {
        self.0.height = height;
    }
    pub fn height(&self) -> Height {
        self.0.height
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

impl From<UpgradeClient> for AbciEvent {
    fn from(v: UpgradeClient) -> Self {
        let attributes = Vec::<Tag>::from(v.0);
        AbciEvent {
            type_str: IbcEventType::UpgradeClient.as_str().to_string(),
            attributes,
        }
    }
}
