//! Types for the IBC events emitted from Tendermint Websocket by the client module.

use serde_derive::{Deserialize, Serialize};

use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::header::AnyHeader;
use crate::core::ics02_client::height::Height;
use crate::core::ics24_host::identifier::ClientId;
use crate::events::IbcEvent;
use crate::prelude::*;

/// NewBlock event signals the committing & execution of a new block.
// TODO - find a better place for NewBlock
#[derive(Debug, Deserialize, Serialize, Clone, Copy, PartialEq, Eq)]
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
            height: Height::default(),
            client_id: Default::default(),
            client_type: ClientType::Tendermint,
            consensus_height: Height::default(),
        }
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
#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

impl core::fmt::Display for CreateClient {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

/// UpdateClient event signals a recent update of an on-chain client (IBC Client).
#[derive(Deserialize, Serialize, Clone, PartialEq, Eq)]
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
#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
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

/// Signals a recent upgrade of an on-chain client (IBC Client).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
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
