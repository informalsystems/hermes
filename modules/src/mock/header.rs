use std::convert::{TryFrom, TryInto};

use tendermint_proto::Protobuf;

use ibc_proto::ibc::mock::Header as RawMockHeader;

use crate::ics02_client::client_def::{AnyConsensusState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::header::Header;
use crate::ics02_client::Error;
use crate::mock::client_state::MockConsensusState;
use crate::Height;

#[derive(Copy, Clone, Default, Debug, PartialEq, Eq)]
pub struct MockHeader(pub Height);

impl Protobuf<RawMockHeader> for MockHeader {}

impl TryFrom<RawMockHeader> for MockHeader {
    type Error = Error;

    fn try_from(raw: RawMockHeader) -> Result<Self, Self::Error> {
        Ok(MockHeader(
            raw.height.ok_or(Error::EmptyRawHeader)?.try_into()?,
        ))
    }
}

impl From<MockHeader> for RawMockHeader {
    fn from(value: MockHeader) -> Self {
        value.into()
    }
}

impl MockHeader {
    pub fn height(&self) -> Height {
        self.0
    }
}

impl From<MockHeader> for AnyHeader {
    fn from(mh: MockHeader) -> Self {
        Self::Mock(mh)
    }
}

impl Header for MockHeader {
    fn client_type(&self) -> ClientType {
        ClientType::Mock
    }

    fn height(&self) -> Height {
        todo!()
    }

    fn wrap_any(self) -> AnyHeader {
        todo!()
    }
}

impl From<MockHeader> for AnyConsensusState {
    fn from(h: MockHeader) -> Self {
        AnyConsensusState::Mock(MockConsensusState(h))
    }
}
