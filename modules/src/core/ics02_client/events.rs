//! Types for the IBC events emitted from Tendermint Websocket by the client module.

use serde_derive::{Deserialize, Serialize};
use tendermint::abci::tag::Tag;
use tendermint::abci::Event as AbciEvent;

use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::header::AnyHeader;
use crate::core::ics02_client::height::Height;
use crate::core::ics24_host::identifier::ClientId;
use crate::events::{IbcEvent, IbcEventType};
use crate::prelude::*;

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

/// Convert attributes to Tendermint ABCI tags
///
/// # Note
/// The parsing of `Key`s and `Value`s never fails, because the
/// `FromStr` instance of `tendermint::abci::tag::{Key, Value}`
/// is infallible, even if it is not represented in the error type.
/// Once tendermint-rs improves the API of the `Key` and `Value` types,
/// we will be able to remove the `.parse().unwrap()` calls.
impl From<Attributes> for Vec<Tag> {
    fn from(attrs: Attributes) -> Self {
        let client_id = Tag {
            key: CLIENT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: attrs.client_id.to_string().parse().unwrap(),
        };
        let client_type = Tag {
            key: CLIENT_TYPE_ATTRIBUTE_KEY.parse().unwrap(),
            value: attrs.client_type.as_str().parse().unwrap(),
        };
        let consensus_height = Tag {
            key: CONSENSUS_HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: attrs.consensus_height.to_string().parse().unwrap(),
        };
        vec![client_id, client_type, consensus_height]
    }
}

impl core::fmt::Display for Attributes {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "cs_h: {}({})", self.client_id, self.consensus_height)
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

impl From<Attributes> for CreateClient {
    fn from(attrs: Attributes) -> Self {
        CreateClient(attrs)
    }
}

impl TryFrom<&AbciEvent> for CreateClient {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        extract_attributes_from_tx(abci_event).map(CreateClient)
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

impl TryFrom<&AbciEvent> for UpdateClient {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        extract_attributes_from_tx(abci_event).map(|attributes| UpdateClient {
            common: attributes,
            header: extract_header_from_tx(abci_event).ok(),
        })
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
}

impl From<Attributes> for ClientMisbehaviour {
    fn from(attrs: Attributes) -> Self {
        ClientMisbehaviour(attrs)
    }
}

impl TryFrom<&AbciEvent> for ClientMisbehaviour {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        extract_attributes_from_tx(abci_event).map(ClientMisbehaviour)
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
    pub fn client_id(&self) -> &ClientId {
        &self.0.client_id
    }
}

impl From<Attributes> for UpgradeClient {
    fn from(attrs: Attributes) -> Self {
        UpgradeClient(attrs)
    }
}

impl TryFrom<&AbciEvent> for UpgradeClient {
    type Error = Error;

    fn try_from(abci_event: &AbciEvent) -> Result<Self, Self::Error> {
        extract_attributes_from_tx(abci_event).map(UpgradeClient)
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

fn extract_attributes_from_tx(event: &AbciEvent) -> Result<Attributes, Error> {
    let mut attr = Attributes::default();

    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        match key {
            CLIENT_ID_ATTRIBUTE_KEY => {
                attr.client_id = value.parse().map_err(Error::invalid_client_identifier)?
            }
            CLIENT_TYPE_ATTRIBUTE_KEY => {
                attr.client_type = value
                    .parse()
                    .map_err(|_| Error::unknown_client_type(value.to_string()))?
            }
            CONSENSUS_HEIGHT_ATTRIBUTE_KEY => {
                attr.consensus_height = value
                    .parse()
                    .map_err(|e| Error::invalid_string_as_height(value.to_string(), e))?
            }
            _ => {}
        }
    }

    Ok(attr)
}

pub fn extract_header_from_tx(event: &AbciEvent) -> Result<AnyHeader, Error> {
    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        if key == HEADER_ATTRIBUTE_KEY {
            return AnyHeader::decode_from_string(value);
        }
    }
    Err(Error::missing_raw_header())
}

#[cfg(test)]
mod tests {
    use crate::core::ics02_client::header::Header;
    use crate::mock::header::MockHeader;

    use super::*;

    #[test]
    fn client_event_to_abci_event() {
        let consensus_height = Height::new(1, 1).unwrap();
        let attributes = Attributes {
            client_id: "test_client".parse().unwrap(),
            client_type: ClientType::Tendermint,
            consensus_height,
        };
        let mut abci_events = vec![];
        let create_client = CreateClient::from(attributes.clone());
        abci_events.push(AbciEvent::from(create_client.clone()));
        let client_misbehaviour = ClientMisbehaviour::from(attributes.clone());
        abci_events.push(AbciEvent::from(client_misbehaviour.clone()));
        let upgrade_client = UpgradeClient::from(attributes.clone());
        abci_events.push(AbciEvent::from(upgrade_client.clone()));
        let mut update_client = UpdateClient::from(attributes);
        let header = MockHeader::new(consensus_height).wrap_any();
        update_client.header = Some(header);
        abci_events.push(AbciEvent::from(update_client.clone()));

        for abci_event in abci_events {
            match IbcEvent::try_from(&abci_event).ok() {
                Some(ibc_event) => match ibc_event {
                    IbcEvent::CreateClient(e) => assert_eq!(e.0, create_client.0),
                    IbcEvent::ClientMisbehaviour(e) => assert_eq!(e.0, client_misbehaviour.0),
                    IbcEvent::UpgradeClient(e) => assert_eq!(e.0, upgrade_client.0),
                    IbcEvent::UpdateClient(e) => {
                        assert_eq!(e.common, update_client.common);
                        assert_eq!(e.header, update_client.header);
                    }
                    _ => panic!("unexpected event type"),
                },
                None => panic!("converted event was wrong"),
            }
        }
    }
}
