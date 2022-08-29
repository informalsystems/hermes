#[cfg(test)]
pub mod mock;
pub mod tendermint;

use core::ops::Deref;

use ibc::clients::ics07_tendermint::header::{
    decode_header, Header as TendermintHeader, TENDERMINT_HEADER_TYPE_URL,
};
use ibc::core::ics02_client::client_type::ClientType;
use ibc::core::ics02_client::error::Error;
use ibc::core::ics02_client::events::UpdateClient;
use ibc::core::ics02_client::header::Header;
#[cfg(test)]
use ibc::mock::header::{MockHeader, MOCK_HEADER_TYPE_URL};
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::lightclients::tendermint::v1::Header as RawTmHeader;
#[cfg(test)]
use ibc_proto::ibc::mock::Header as RawMockHeader;
use ibc_proto::protobuf::Protobuf as ErasedProtobuf;
use serde::{Deserialize, Serialize};
use subtle_encoding::hex;

use crate::chain::endpoint::ChainEndpoint;
use crate::client_state::AnyClientState;
use crate::error;
use crate::misbehaviour::MisbehaviourEvidence;

/// Defines a light block from the point of view of the relayer.
pub trait LightBlock<C: ChainEndpoint>: Send + Sync {
    fn signed_header(&self) -> &C::Header;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verified<H> {
    /// Verified target
    pub target: H,
    /// Supporting headers needed to verify `target`
    pub supporting: Vec<H>,
}

/// Defines a client from the point of view of the relayer.
pub trait LightClient<C: ChainEndpoint>: Send + Sync {
    /// Fetch and verify a header, and return its minimal supporting set.
    fn header_and_minimal_set(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<C::Header>, error::Error>;

    /// Fetch a header from the chain at the given height and verify it.
    fn verify(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<C::LightBlock>, error::Error>;

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, error::Error>;

    /// Fetch a header from the chain at the given height, without verifying it
    fn fetch(&mut self, height: Height) -> Result<C::LightBlock, error::Error>;
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Tendermint(TendermintHeader),
    #[cfg(test)]
    Mock(MockHeader),
}

impl Header for AnyHeader {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(header) => header.client_type(),

            #[cfg(test)]
            Self::Mock(header) => header.client_type(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(header) => header.height(),

            #[cfg(test)]
            Self::Mock(header) => header.height(),
        }
    }

    fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(header) => header.timestamp(),

            #[cfg(test)]
            Self::Mock(header) => header.timestamp(),
        }
    }
}

impl AnyHeader {
    pub fn encode_to_string(&self) -> String {
        let buf = ErasedProtobuf::encode_vec(self).expect("encoding shouldn't fail");
        let encoded = hex::encode(buf);
        String::from_utf8(encoded).expect("hex-encoded string should always be valid UTF-8")
    }

    pub fn decode_from_string(s: &str) -> Result<Self, Error> {
        let header_bytes = hex::decode(s).unwrap();
        ErasedProtobuf::decode(header_bytes.as_ref()).map_err(Error::invalid_raw_header)
    }
}

impl ErasedProtobuf<Any> for AnyHeader {}

impl TryFrom<Any> for AnyHeader {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Error> {
        match raw.type_url.as_str() {
            TENDERMINT_HEADER_TYPE_URL => {
                let val = decode_header(raw.value.deref())?;

                Ok(AnyHeader::Tendermint(val))
            }

            #[cfg(test)]
            MOCK_HEADER_TYPE_URL => Ok(AnyHeader::Mock(
                ErasedProtobuf::<RawMockHeader>::decode_vec(&raw.value)
                    .map_err(Error::invalid_raw_header)?,
            )),

            _ => Err(Error::unknown_header_type(raw.type_url)),
        }
    }
}

impl From<AnyHeader> for Any {
    fn from(value: AnyHeader) -> Self {
        match value {
            AnyHeader::Tendermint(header) => Any {
                type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
                value: ErasedProtobuf::<RawTmHeader>::encode_vec(&header)
                    .expect("encoding to `Any` from `AnyHeader::Tendermint`"),
            },

            #[cfg(test)]
            AnyHeader::Mock(header) => Any {
                type_url: MOCK_HEADER_TYPE_URL.to_string(),
                value: ErasedProtobuf::<RawMockHeader>::encode_vec(&header)
                    .expect("encoding to `Any` from `AnyHeader::Mock`"),
            },
        }
    }
}

impl From<TendermintHeader> for AnyHeader {
    fn from(header: TendermintHeader) -> Self {
        Self::Tendermint(header)
    }
}

#[cfg(test)]
impl From<MockHeader> for AnyHeader {
    fn from(header: MockHeader) -> Self {
        Self::Mock(header)
    }
}
