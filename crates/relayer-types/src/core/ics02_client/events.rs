//! Types for the IBC events emitted from Tendermint Websocket by the client module.

use serde_derive::{Deserialize, Serialize};
use std::fmt::{Display, Error as FmtError, Formatter};
use tendermint::abci;

use super::header::Header;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::height::Height;
use crate::core::ics24_host::identifier::ClientId;
use crate::events::{IbcEvent, IbcEventType};

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

impl Display for NewBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "NewBlock {{ height: {} }}", self.height)
    }
}

impl From<NewBlock> for IbcEvent {
    fn from(v: NewBlock) -> Self {
        IbcEvent::NewBlock(v)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Attributes {
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub consensus_height: Height,
}

impl Default for Attributes {
    fn default() -> Self {
        Attributes {
            client_id: Default::default(),
            client_type: ClientType::Tendermint,
            consensus_height: Height::new(0, 1).unwrap(),
        }
    }
}

impl Display for Attributes {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "Attributes {{ client_id: {}, client_type: {}, consensus_height: {} }}",
            self.client_id, self.client_type, self.consensus_height
        )
    }
}

/// Convert attributes to Tendermint ABCI tags
impl From<Attributes> for Vec<abci::EventAttribute> {
    fn from(attrs: Attributes) -> Self {
        let client_id = (CLIENT_ID_ATTRIBUTE_KEY, attrs.client_id.as_str()).into();
        let client_type = (CLIENT_TYPE_ATTRIBUTE_KEY, attrs.client_type.as_str()).into();
        let consensus_height = (
            CONSENSUS_HEIGHT_ATTRIBUTE_KEY,
            attrs.consensus_height.to_string(),
        )
            .into();
        vec![client_id, client_type, consensus_height]
    }
}

/// CreateClient event signals the creation of a new on-chain client (IBC client).
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct CreateClient(pub Attributes);

impl CreateClient {
    pub fn client_id(&self) -> &ClientId {
        &self.0.client_id
    }
}

impl Display for CreateClient {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "CreateClient {{ {} }}", self.0)
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

impl From<CreateClient> for abci::Event {
    fn from(v: CreateClient) -> Self {
        Self {
            kind: IbcEventType::CreateClient.as_str().to_owned(),
            attributes: v.0.into(),
        }
    }
}

/// UpdateClient event signals a recent update of an on-chain client (IBC Client).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct UpdateClient {
    pub common: Attributes,
    pub header: Option<Box<dyn Header>>,
}

impl UpdateClient {
    pub fn client_id(&self) -> &ClientId {
        &self.common.client_id
    }

    pub fn client_type(&self) -> ClientType {
        self.common.client_type
    }

    pub fn consensus_height(&self) -> Height {
        self.common.consensus_height
    }
}

impl Display for UpdateClient {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        // TODO Display: Check for a solution for Box<dyn Header>
        write!(
            f,
            "UpdateClient {{ common: {}, header: None }}",
            self.common
        )
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

impl From<UpdateClient> for abci::Event {
    fn from(v: UpdateClient) -> Self {
        let mut attributes: Vec<_> = v.common.into();
        if let Some(h) = v.header {
            let header = (HEADER_ATTRIBUTE_KEY, h.encode_to_hex_string()).into();
            attributes.push(header);
        }
        Self {
            kind: IbcEventType::UpdateClient.as_str().to_string(),
            attributes,
        }
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
}

impl Display for ClientMisbehaviour {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "ClientMisbehaviour {{ {} }}", self.0)
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

impl From<ClientMisbehaviour> for abci::Event {
    fn from(v: ClientMisbehaviour) -> Self {
        Self {
            kind: IbcEventType::ClientMisbehaviour.as_str().to_owned(),
            attributes: v.0.into(),
        }
    }
}

/// Signals a recent upgrade of an on-chain client (IBC Client).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct UpgradeClient(pub Attributes);

impl UpgradeClient {
    pub fn client_id(&self) -> &ClientId {
        &self.0.client_id
    }
}

impl Display for UpgradeClient {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "UpgradeClient {{ {} }}", self.0)
    }
}

impl From<Attributes> for UpgradeClient {
    fn from(attrs: Attributes) -> Self {
        UpgradeClient(attrs)
    }
}

impl From<UpgradeClient> for abci::Event {
    fn from(v: UpgradeClient) -> Self {
        Self {
            kind: IbcEventType::UpgradeClient.as_str().to_owned(),
            attributes: v.0.into(),
        }
    }
}
