use core::fmt::Debug;

use serde::{Deserialize, Serialize};

use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;

use crate::clients::ics07_tendermint::header::{
    decode_header as tm_decode_header, Header as TendermintHeader, TENDERMINT_HEADER_TYPE_URL,
};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::timestamp::Timestamp;
use crate::Height;

use crate::clients::ics06_solomachine::header::{
    decode_header as sm_decode_header, Header as SolomachineHeader, SOLOMACHINE_HEADER_TYPE_URL,
};
use crate::clients::ics12_near::header::{
    decode_header as near_decode_header, Header as NearHeader, NEAR_HEADER_TYPE_URL,
};

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
    // For now, we only have tendermint; however when there is more than one, we
    // can try decoding into all the known types, and return an error only if
    // none work
    let header: TendermintHeader =
        Protobuf::<Any>::decode(header_bytes).map_err(Error::invalid_raw_header)?;

    Ok(AnyHeader::Tendermint(header))
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Tendermint(TendermintHeader),
    Solomachine(SolomachineHeader),
    Near(NearHeader),
}

impl Header for AnyHeader {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(header) => header.client_type(),
            Self::Solomachine(header) => header.client_type(),
            Self::Near(header) => header.client_type(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(header) => header.height(),
            Self::Solomachine(header) => header.height(),
            Self::Near(header) => header.height(),
        }
    }

    fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(header) => header.timestamp(),
            Self::Solomachine(header) => header.timestamp(),
            Self::Near(header) => header.timestamp(),
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
            SOLOMACHINE_HEADER_TYPE_URL => {
                let val = sm_decode_header(raw.value.as_slice())?;
                Ok(AnyHeader::Solomachine(val))
            }
            NEAR_HEADER_TYPE_URL => {
                let val = near_decode_header(raw.value.as_slice())?;
                Ok(AnyHeader::Near(val))
            }

            _ => Err(Error::unknown_header_type(raw.type_url)),
        }
    }
}

impl From<AnyHeader> for Any {
    fn from(value: AnyHeader) -> Self {
        use ibc_proto::ibc::lightclients::solomachine::v3::Header as RawSmHeader;
        use ibc_proto::ibc::lightclients::tendermint::v1::Header as RawTmHeader;
        use ics12_proto::v1::Header as RawNearHeader;

        match value {
            AnyHeader::Tendermint(header) => Any {
                type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
                value: Protobuf::<RawTmHeader>::encode_vec(header),
            },
            AnyHeader::Solomachine(header) => Any {
                type_url: SOLOMACHINE_HEADER_TYPE_URL.to_string(),
                value: Protobuf::<RawSmHeader>::encode_vec(header),
            },
            AnyHeader::Near(header) => Any {
                type_url: NEAR_HEADER_TYPE_URL.to_string(),
                value: Protobuf::<RawNearHeader>::encode_vec(header),
            },
        }
    }
}

impl From<TendermintHeader> for AnyHeader {
    fn from(header: TendermintHeader) -> Self {
        Self::Tendermint(header)
    }
}

impl From<SolomachineHeader> for AnyHeader {
    fn from(header: SolomachineHeader) -> Self {
        Self::Solomachine(header)
    }
}

impl From<NearHeader> for AnyHeader {
    fn from(header: NearHeader) -> Self {
        Self::Near(header)
    }
}
