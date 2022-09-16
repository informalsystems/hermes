use crate::prelude::*;

use tendermint_proto::Protobuf;

use ibc_proto::ibc::mock::Misbehaviour as RawMisbehaviour;

use crate::{
	core::{
		ics02_client::{error::Error, misbehaviour::Misbehaviour},
		ics24_host::identifier::ClientId,
	},
	mock::header::MockHeader,
	Height,
};
use ibc_proto::google::protobuf::Any;

pub const MOCK_MISBEHAVIOUR_TYPE_URL: &str = "/ibc.mock.Misbehavior";

#[derive(Clone, Debug, PartialEq, Misbehaviour, Protobuf)]
#[allow(clippy::large_enum_variant)]
pub enum AnyMisbehaviour {
	#[ibc(proto_url = "MOCK_MISBEHAVIOUR_TYPE_URL")]
	Mock(MockMisbehaviour),
}

#[derive(Clone, Debug, PartialEq)]
pub struct MockMisbehaviour {
	pub client_id: ClientId,
	pub header1: MockHeader,
	pub header2: MockHeader,
}

impl Misbehaviour for MockMisbehaviour {
	fn client_id(&self) -> &ClientId {
		&self.client_id
	}

	fn height(&self) -> Height {
		self.header1.height()
	}

	fn encode_to_vec(&self) -> Vec<u8> {
		self.encode_vec()
	}
}

impl Protobuf<RawMisbehaviour> for MockMisbehaviour {}

impl TryFrom<RawMisbehaviour> for MockMisbehaviour {
	type Error = Error;

	fn try_from(raw: RawMisbehaviour) -> Result<Self, Self::Error> {
		Ok(Self {
			client_id: Default::default(),
			header1: raw.header1.ok_or_else(Error::missing_raw_misbehaviour)?.try_into()?,
			header2: raw.header2.ok_or_else(Error::missing_raw_misbehaviour)?.try_into()?,
		})
	}
}

impl From<MockMisbehaviour> for RawMisbehaviour {
	fn from(value: MockMisbehaviour) -> Self {
		RawMisbehaviour {
			client_id: value.client_id.to_string(),
			header1: Some(value.header1.into()),
			header2: Some(value.header2.into()),
		}
	}
}
