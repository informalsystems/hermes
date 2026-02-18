use core::fmt::Debug;

use serde::{Deserialize, Serialize};

use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;

use crate::clients::ics07_tendermint::header::{
    decode_header as tm_decode_header, Header as TendermintHeader, TENDERMINT_HEADER_TYPE_URL,
};
use crate::clients::ics08_cardano::header::{Header as MithrilHeader, MITHRIL_HEADER_TYPE_URL};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::timestamp::Timestamp;
use crate::Height;

/// Abstract of consensus state update information
pub trait Header: Debug + Send + Sync // Any: From<Self>,
{
    /// The type of client (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// The height of the consensus state
    fn height(&self) -> Height;

    /// The timestamp of the consensus state
    fn timestamp(&self) -> Timestamp;
}

/// Decodes an encoded header into a known `Header` type,
pub fn decode_header(header_bytes: &[u8]) -> Result<AnyHeader, Error> {
    let raw_any: Any = Any::decode(header_bytes).map_err(Error::decode)?;
    AnyHeader::try_from(raw_any)
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Tendermint(TendermintHeader),
    Mithril(MithrilHeader),
}

impl Header for AnyHeader {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(header) => header.client_type(),
            Self::Mithril(header) => header.client_type(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(header) => header.height(),
            Self::Mithril(header) => header.height(),
        }
    }

    fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(header) => header.timestamp(),
            Self::Mithril(header) => header.timestamp(),
        }
    }
}

impl Protobuf<Any> for AnyHeader {}

impl TryFrom<Any> for AnyHeader {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Error> {
        match raw.type_url.as_str() {
            TENDERMINT_HEADER_TYPE_URL => {
                let val = tm_decode_header(raw.value.as_slice())?;
                Ok(AnyHeader::Tendermint(val))
            }
            MITHRIL_HEADER_TYPE_URL => {
                let val: MithrilHeader = raw.try_into()?;
                Ok(AnyHeader::Mithril(val))
            }

            _ => Err(Error::unknown_header_type(raw.type_url)),
        }
    }
}

impl From<AnyHeader> for Any {
    fn from(value: AnyHeader) -> Self {
        use ibc_proto::ibc::lightclients::tendermint::v1::Header as RawHeader;

        match value {
            AnyHeader::Tendermint(header) => Any {
                type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
                value: Protobuf::<RawHeader>::encode_vec(header),
            },
            AnyHeader::Mithril(header) => header.into(),
        }
    }
}

impl From<TendermintHeader> for AnyHeader {
    fn from(header: TendermintHeader) -> Self {
        Self::Tendermint(header)
    }
}

impl From<MithrilHeader> for AnyHeader {
    fn from(header: MithrilHeader) -> Self {
        Self::Mithril(header)
    }
}
