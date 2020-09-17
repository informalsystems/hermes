use crate::ics02_client::client_def::AnyHeader;
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::{self, Error};
use crate::ics02_client::header::Header;
use crate::try_from_raw::TryFromRaw;

use serde_derive::{Deserialize, Serialize};
use tendermint::block::Height;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockHeader(pub Height);

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

impl TryFromRaw for MockHeader {
    type Error = Error;
    type RawType = ibc_proto::ibc::mock::Header;

    fn try_from(raw: Self::RawType) -> Result<Self, Self::Error> {
        let proto_height = raw.height.ok_or_else(|| error::Kind::InvalidRawHeader)?;
        Ok(Self(decode_height(proto_height)))
    }
}

fn decode_height(height: ibc_proto::ibc::client::Height) -> Height {
    Height(height.epoch_height) // FIXME: This is wrong as it does not take the epoch into account
}
