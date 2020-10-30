use std::convert::{TryFrom, TryInto};

use ibc_proto::ibc::mock::Header as RawMockHeader;
use tendermint_proto::DomainType;

use crate::ics02_client::client_def::{AnyConsensusState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::{self, Error};
use crate::ics02_client::header::Header;
use crate::mock_client::state::MockConsensusState;
use crate::Height;

#[derive(Copy, Clone, Default, Debug, PartialEq, Eq)]
pub struct MockHeader(pub Height);

impl DomainType<RawMockHeader> for MockHeader {}

impl TryFrom<RawMockHeader> for MockHeader {
    type Error = Error;

    fn try_from(raw: RawMockHeader) -> Result<Self, Self::Error> {
        if raw.height.is_none() {
            return Err(error::Kind::InvalidRawHeader
                .context("no height in header")
                .into());
        }

        Ok(MockHeader(
            raw.height
                .ok_or_else(|| error::Kind::InvalidRawHeader)?
                .try_into()
                .map_err(|e| error::Kind::InvalidRawHeader.context(e))?,
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
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
    }
}

impl From<MockHeader> for AnyConsensusState {
    fn from(h: MockHeader) -> Self {
        AnyConsensusState::Mock(MockConsensusState(h))
    }
}
