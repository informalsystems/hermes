//! Types for the IBC events emitted from Tendermint Websocket by the client module.

use crate::{
	core::{ics02_client::height::Height, ics24_host::identifier::ClientId},
	events::IbcEvent,
	prelude::*,
};
use serde_derive::{Deserialize, Serialize};
use tendermint::abci::EventAttribute;

/// The content of the `key` field for the attribute containing the height.
const HEIGHT_ATTRIBUTE_KEY: &str = "height";

/// The content of the `key` field for the attribute containing the client identifier.
const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";

/// The content of the `key` field for the attribute containing the client type.
const CLIENT_TYPE_ATTRIBUTE_KEY: &str = "client_type";

/// The content of the `key` field for the attribute containing the height.
const CONSENSUS_HEIGHT_ATTRIBUTE_KEY: &str = "consensus_height";

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
	pub client_type: String,
	pub consensus_height: Height,
}

#[cfg(not(test))]
impl Default for Attributes {
	fn default() -> Self {
		Attributes {
			height: Height::default(),
			client_id: Default::default(),
			client_type: "00-uninitialized".to_owned(),
			consensus_height: Height::default(),
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
impl From<Attributes> for Vec<EventAttribute> {
	fn from(a: Attributes) -> Self {
		let height = EventAttribute {
			key: HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
			value: a.height.to_string().parse().unwrap(),
			index: false,
		};
		let client_id = EventAttribute {
			key: CLIENT_ID_ATTRIBUTE_KEY.parse().unwrap(),
			value: a.client_id.to_string().parse().unwrap(),
			index: false,
		};
		let client_type = EventAttribute {
			key: CLIENT_TYPE_ATTRIBUTE_KEY.parse().unwrap(),
			value: a.client_type.to_owned(),
			index: false,
		};
		let consensus_height = EventAttribute {
			key: CONSENSUS_HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
			value: a.height.to_string().parse().unwrap(),
			index: false,
		};
		vec![height, client_id, client_type, consensus_height]
	}
}

impl core::fmt::Display for Attributes {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
		write!(f, "h: {}, cs_h: {}({})", self.height, self.client_id, self.consensus_height)
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
// TODO: use generic header type
#[derive(Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct UpdateClient {
	pub common: Attributes,
	pub header: Option<Vec<u8>>,
}

impl UpdateClient {
	pub fn client_id(&self) -> &ClientId {
		&self.common.client_id
	}

	pub fn client_type(&self) -> &str {
		&self.common.client_type
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
		UpdateClient { common: attrs, header: None }
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
