use crate::ics02_client::client_def::AnyHeader;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::{self, Error};
use crate::ics02_client::header::Header;

use ibc_proto::ibc::mock::Header as RawMockHeader;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::block::Height;
use tendermint_proto::DomainType;

#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
        Ok(MockHeader(Height(raw.height.unwrap().epoch_height)))
    }
}

impl From<MockHeader> for RawMockHeader {
    fn from(value: MockHeader) -> Self {
        RawMockHeader {
            height: Some(ibc_proto::ibc::client::Height {
                epoch_number: 0,
                epoch_height: value.height().value(),
            }),
        } // FIXME: This is wrong as it does not take the epoch into account
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
