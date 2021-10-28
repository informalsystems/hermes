use crate::prelude::*;

use tendermint_proto::Protobuf;

use ibc_proto::ibc::mock::Misbehaviour as RawMisbehaviour;

use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::misbehaviour::AnyMisbehaviour;
use crate::core::ics24_host::identifier::ClientId;
use crate::mock::header::MockHeader;
use crate::Height;

#[derive(Clone, Debug, PartialEq)]
pub struct Misbehaviour {
    pub client_id: ClientId,
    pub header1: MockHeader,
    pub header2: MockHeader,
}

impl crate::core::ics02_client::misbehaviour::Misbehaviour for Misbehaviour {
    fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    fn height(&self) -> Height {
        self.header1.height()
    }

    fn wrap_any(self) -> AnyMisbehaviour {
        AnyMisbehaviour::Mock(self)
    }
}

impl Protobuf<RawMisbehaviour> for Misbehaviour {}

impl TryFrom<RawMisbehaviour> for Misbehaviour {
    type Error = Error;

    fn try_from(raw: RawMisbehaviour) -> Result<Self, Self::Error> {
        Ok(Self {
            client_id: Default::default(),
            header1: raw
                .header1
                .ok_or_else(Error::missing_raw_misbehaviour)?
                .try_into()?,
            header2: raw
                .header2
                .ok_or_else(Error::missing_raw_misbehaviour)?
                .try_into()?,
        })
    }
}

impl From<Misbehaviour> for RawMisbehaviour {
    fn from(value: Misbehaviour) -> Self {
        RawMisbehaviour {
            client_id: value.client_id.to_string(),
            header1: Some(value.header1.into()),
            header2: Some(value.header2.into()),
        }
    }
}
