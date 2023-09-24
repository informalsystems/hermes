use super::consensus_state::PublicKey;
use super::error::Error;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::timestamp::Timestamp;
use crate::Height;
use bytes::Buf;
use core::fmt::{Error as FmtError, Formatter};
use cosmos_sdk_proto::{self, traits::Message};
use eyre::Result;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::lightclients::solomachine::v3::Header as RawHeader;
use ibc_proto::ibc::lightclients::solomachine::v3::HeaderData as RawHeaderData;
use ibc_proto::protobuf::Protobuf;
use serde::{Deserialize, Serialize};

pub const SOLOMACHINE_HEADER_TYPE_URL: &str = "/ibc.lightclients.solomachine.v3.Header";

#[derive(Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct Header {
    pub timestamp: Timestamp,
    pub signature: Vec<u8>,
    pub new_public_key: PublicKey,
    pub new_diversifier: String,
}

impl crate::core::ics02_client::header::Header for Header {
    fn client_type(&self) -> ClientType {
        ClientType::Solomachine
    }

    fn height(&self) -> Height {
        Height::new(0, 41).expect("faild to contruct ibc height")
    }

    fn timestamp(&self) -> Timestamp {
        self.timestamp
    }
}

impl core::fmt::Debug for Header {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, " Header {{...}}")
    }
}

impl Protobuf<RawHeader> for Header {}

impl TryFrom<RawHeader> for Header {
    type Error = Error;

    fn try_from(raw: RawHeader) -> Result<Self, Self::Error> {
        let new_public_key =
            PublicKey::try_from(raw.new_public_key.ok_or(Error::public_key_is_empty())?)
                .map_err(Error::public_key_parse_failed)?;

        let timestamp =
            Timestamp::from_nanoseconds(raw.timestamp).map_err(Error::parse_timestamp_error)?;
        let header = Self {
            timestamp,
            signature: raw.signature,
            new_public_key,
            new_diversifier: raw.new_diversifier,
        };

        Ok(header)
    }
}

impl Protobuf<Any> for Header {}

impl TryFrom<Any> for Header {
    type Error = Ics02Error;

    fn try_from(raw: Any) -> Result<Self, Ics02Error> {
        use core::ops::Deref;

        fn decode_header<B: Buf>(buf: B) -> Result<Header, Error> {
            RawHeader::decode(buf).map_err(Error::decode)?.try_into()
        }

        match raw.type_url.as_str() {
            SOLOMACHINE_HEADER_TYPE_URL => decode_header(raw.value.deref()).map_err(Into::into),
            _ => Err(Ics02Error::unknown_header_type(raw.type_url)),
        }
    }
}

impl From<Header> for Any {
    fn from(header: Header) -> Self {
        Any {
            type_url: SOLOMACHINE_HEADER_TYPE_URL.to_string(),
            value: Protobuf::<RawHeader>::encode_vec(&header),
        }
    }
}

pub fn decode_header<B: Buf>(buf: B) -> Result<Header, Error> {
    RawHeader::decode(buf).map_err(Error::decode)?.try_into()
}

impl From<Header> for RawHeader {
    fn from(value: Header) -> Self {
        RawHeader {
            timestamp: value.timestamp.nanoseconds(),
            signature: value.signature,
            new_public_key: Some(
                value
                    .new_public_key
                    .to_any()
                    .expect("Unknow Public Key Type"),
            ),
            new_diversifier: value.new_diversifier,
        }
    }
}

/// HeaderData returns the SignBytes data for update verification.
#[derive(Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct HeaderData {
    /// header public key
    pub new_pub_key: PublicKey,
    /// header diversifier
    pub new_diversifier: String,
}

impl Protobuf<RawHeaderData> for HeaderData {}

impl TryFrom<RawHeaderData> for HeaderData {
    type Error = Error;

    fn try_from(raw: RawHeaderData) -> Result<Self, Self::Error> {
        let new_public_key =
            PublicKey::try_from(raw.new_pub_key.ok_or(Error::public_key_is_empty())?)
                .map_err(Error::public_key_parse_failed)?;

        Ok(Self {
            new_pub_key: new_public_key,
            new_diversifier: raw.new_diversifier,
        })
    }
}

impl From<HeaderData> for RawHeaderData {
    fn from(value: HeaderData) -> Self {
        RawHeaderData {
            new_pub_key: Some(value.new_pub_key.to_any().expect("Unknow Public Key Type")),
            new_diversifier: value.new_diversifier,
        }
    }
}
