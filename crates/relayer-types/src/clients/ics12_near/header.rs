use crate::clients::ics12_near::near_types::hash::CryptoHash;
use crate::clients::ics12_near::near_types::LightClientBlock;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::timestamp::Timestamp;
use crate::Height;
use bytes::Buf;
use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use serde::{Deserialize, Serialize};
pub const NEAR_HEADER_TYPE_URL: &str = "/ibc.lightclients.near.v1.Header";
use borsh::{to_vec, BorshDeserialize};
use ics12_proto::v1::{CryptoHash as RawCryptoHash, Header as RawHeader};
use prost::Message;

#[derive(Default, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Header {
    pub light_client_block: LightClientBlock,
    pub prev_state_root_of_chunks: Vec<CryptoHash>,
}

impl crate::core::ics02_client::header::Header for Header {
    fn client_type(&self) -> ClientType {
        ClientType::Near
    }

    fn height(&self) -> Height {
        Height::new(0, self.light_client_block.inner_lite.height)
            .expect("failed to create ibc height") // TODO: julian, see revision number in tm header
    }

    fn timestamp(&self) -> Timestamp {
        Timestamp::from_nanoseconds(self.light_client_block.inner_lite.timestamp)
            .expect("failed to create Timestamp")
    }
}

impl Protobuf<RawHeader> for Header {}

impl TryFrom<RawHeader> for Header {
    type Error = Error;

    fn try_from(raw: RawHeader) -> Result<Self, Self::Error> {
        let header = Self {
            light_client_block: LightClientBlock::try_from_slice(&raw.light_client_block)
                .map_err(|e| Error::custom_error(e.to_string()))?,
            prev_state_root_of_chunks: raw
                .prev_state_root_of_chunks
                .iter()
                .map(|c| CryptoHash::try_from(&c.raw_data[..]))
                .collect::<Result<Vec<CryptoHash>, _>>()
                .map_err(|e| Error::custom_error(e.to_string()))?,
        };

        Ok(header)
    }
}

impl From<Header> for RawHeader {
    fn from(value: Header) -> Self {
        RawHeader {
            light_client_block: to_vec(&value.light_client_block)
                .expect("failed serialize to light client block"),
            prev_state_root_of_chunks: value
                .prev_state_root_of_chunks
                .iter()
                .map(|c| RawCryptoHash {
                    raw_data: c.0.to_vec(),
                })
                .collect(),
        }
    }
}

impl Protobuf<Any> for Header {}

impl TryFrom<Any> for Header {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Error> {
        use core::ops::Deref;

        match raw.type_url.as_str() {
            NEAR_HEADER_TYPE_URL => decode_header(raw.value.deref()).map_err(Into::into),
            _ => Err(Error::unknown_header_type(raw.type_url)),
        }
    }
}

impl From<Header> for Any {
    fn from(header: Header) -> Self {
        Any {
            type_url: NEAR_HEADER_TYPE_URL.to_string(),
            value: Protobuf::<RawHeader>::encode_vec(header),
        }
    }
}

pub fn decode_header<B: Buf>(buf: B) -> Result<Header, Error> {
    RawHeader::decode(buf).map_err(Error::decode)?.try_into()
}
