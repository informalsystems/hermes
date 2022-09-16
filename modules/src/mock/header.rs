use serde_derive::{Deserialize, Serialize};
use tendermint_proto::Protobuf;

use ibc_proto::ibc::mock::Header as RawMockHeader;

use crate::{
	core::ics02_client::{error::Error, header::Header},
	mock::client_state::{AnyConsensusState, MockConsensusState},
	timestamp::Timestamp,
	Height,
};
use ibc_proto::google::protobuf::Any;

pub const MOCK_HEADER_TYPE_URL: &str = "/ibc.mock.Header";

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize, Header, Protobuf)]
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
	#[ibc(proto_url = "MOCK_HEADER_TYPE_URL")]
	Mock(MockHeader),
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

impl From<MockHeader> for AnyHeader {
	fn from(mh: MockHeader) -> Self {
		Self::Mock(mh)
	}
}

impl Header for MockHeader {
	fn height(&self) -> Height {
		self.height()
	}

	fn encode_to_vec(&self) -> Vec<u8> {
		self.encode_vec()
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
		let bytes = AnyHeader::Mock(header).encode_vec();

		assert_eq!(
			&bytes,
			&[
				10, 16, 47, 105, 98, 99, 46, 109, 111, 99, 107, 46, 72, 101, 97, 100, 101, 114, 18,
				6, 10, 4, 8, 1, 16, 10
			]
		);
	}
}
