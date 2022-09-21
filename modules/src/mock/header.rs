use ibc_proto::google::protobuf::Any;
use serde_derive::{Deserialize, Serialize};
use tendermint_proto::Protobuf;

use ibc_proto::ibc::mock::Header as RawMockHeader;

use crate::mock::host::{HostBlock, MockHostBlock};
use crate::mock::misbehaviour::{MockMisbehaviour, MOCK_MISBEHAVIOUR_TYPE_URL};
use crate::{
	core::ics02_client::{client_message::ClientMessage, error::Error},
	mock::client_state::{AnyConsensusState, MockConsensusState},
	timestamp::Timestamp,
	Height,
};

pub const MOCK_HEADER_TYPE_URL: &str = "/ibc.mock.Header";

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize, ClientMessage)]
#[allow(clippy::large_enum_variant)]
pub enum AnyClientMessage {
	#[ibc(proto_url = "MOCK_HEADER_TYPE_URL")]
	Mock(MockClientMessage),
}

impl From<MockHostBlock> for AnyClientMessage {
	fn from(block: MockHostBlock) -> Self {
		Self::Mock(MockClientMessage::Header(MockHeader::new(block.height())))
	}
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub enum MockClientMessage {
	Header(MockHeader),
	Misbehaviour(MockMisbehaviour),
}

impl From<MockHeader> for MockClientMessage {
	fn from(header: MockHeader) -> Self {
		Self::Header(header)
	}
}

impl MockClientMessage {
	pub fn header(&self) -> MockHeader {
		match self {
			MockClientMessage::Header(header) => header.clone(),
			MockClientMessage::Misbehaviour(misbehaviour) => misbehaviour.header1.clone(),
		}
	}
}

impl ClientMessage for MockClientMessage {
	fn encode_to_vec(&self) -> Vec<u8> {
		unreachable!()
	}

	fn height(&self) -> Height {
		match self {
			MockClientMessage::Header(header) => header.height,
			MockClientMessage::Misbehaviour(misbehaviour) => misbehaviour.header1.height,
		}
	}
}

impl Protobuf<Any> for AnyClientMessage {}

impl TryFrom<Any> for AnyClientMessage {
	type Error = Error;

	fn try_from(value: Any) -> Result<Self, Self::Error> {
		match value.type_url.as_str() {
			MOCK_HEADER_TYPE_URL => Ok(Self::Mock(MockClientMessage::Header(
				MockHeader::decode_vec(&value.value).map_err(Error::decode_raw_header)?,
			))),
			MOCK_MISBEHAVIOUR_TYPE_URL => Ok(Self::Mock(MockClientMessage::Misbehaviour(
				MockMisbehaviour::decode_vec(&value.value)
					.map_err(Error::decode_raw_misbehaviour)?,
			))),
			_ => Err(Error::unknown_consensus_state_type(value.type_url)),
		}
	}
}

impl From<AnyClientMessage> for Any {
	fn from(client_msg: AnyClientMessage) -> Self {
		match client_msg {
			AnyClientMessage::Mock(MockClientMessage::Header(header)) => {
				Any { type_url: MOCK_HEADER_TYPE_URL.to_string(), value: header.encode_vec() }
			},
			AnyClientMessage::Mock(MockClientMessage::Misbehaviour(misbehaviour)) => Any {
				type_url: MOCK_MISBEHAVIOUR_TYPE_URL.to_string(),
				value: misbehaviour.encode_vec(),
			},
		}
	}
}

#[derive(Copy, Clone, Default, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct MockHeader {
	pub height: Height,
	pub timestamp: Timestamp,
}

impl Protobuf<RawMockHeader> for MockHeader {}

impl TryFrom<RawMockHeader> for MockHeader {
	type Error = Error;

	fn try_from(raw: RawMockHeader) -> Result<Self, Self::Error> {
		Ok(MockHeader {
			height: raw.height.ok_or_else(Error::missing_raw_header)?.into(),

			timestamp: Timestamp::from_nanoseconds(raw.timestamp)
				.map_err(Error::invalid_packet_timestamp)?,
		})
	}
}

impl From<MockHeader> for RawMockHeader {
	fn from(value: MockHeader) -> Self {
		RawMockHeader {
			height: Some(value.height.into()),
			timestamp: value.timestamp.nanoseconds(),
		}
	}
}

impl MockHeader {
	pub fn height(&self) -> Height {
		self.height
	}

	pub fn new(height: Height) -> Self {
		Self { height, timestamp: Timestamp::now() }
	}

	pub fn timestamp(&self) -> Timestamp {
		self.timestamp
	}

	pub fn with_timestamp(self, timestamp: Timestamp) -> Self {
		Self { timestamp, ..self }
	}
}

impl From<MockClientMessage> for AnyClientMessage {
	fn from(client_msg: MockClientMessage) -> Self {
		Self::Mock(client_msg)
	}
}

impl From<MockHeader> for AnyClientMessage {
	fn from(header: MockHeader) -> Self {
		Self::Mock(MockClientMessage::Header(header))
	}
}

impl From<MockMisbehaviour> for AnyClientMessage {
	fn from(misbehaviour: MockMisbehaviour) -> Self {
		Self::Mock(MockClientMessage::Misbehaviour(misbehaviour))
	}
}

impl From<MockHeader> for AnyConsensusState {
	fn from(h: MockHeader) -> Self {
		AnyConsensusState::Mock(MockConsensusState::new(h))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn encode_any() {
		let header = MockHeader::new(Height::new(1, 10)).with_timestamp(Timestamp::none());
		let bytes = AnyClientMessage::from(header).encode_vec();

		assert_eq!(
			&bytes,
			&[
				10, 16, 47, 105, 98, 99, 46, 109, 111, 99, 107, 46, 72, 101, 97, 100, 101, 114, 18,
				6, 10, 4, 8, 1, 16, 10
			]
		);
	}
}
