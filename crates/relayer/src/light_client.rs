pub mod io;
pub mod tendermint;

use core::ops::Deref;

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::lightclients::tendermint::v1::Header as RawTmHeader;
use ibc_proto::protobuf::Protobuf as ErasedProtobuf;
use ibc_relayer_types::clients::ics07_tendermint::header::{
    decode_header as tm_decode_header, Header as TendermintHeader, TENDERMINT_HEADER_TYPE_URL,
};
use ibc_relayer_types::clients::ics12_near::header::{
    decode_header as near_decode_header, Header as NearHeader, NEAR_HEADER_TYPE_URL,
};
use ibc_relayer_types::core::ics02_client::client_type::ClientType;
use ibc_relayer_types::core::ics02_client::error::Error;
use ibc_relayer_types::core::ics02_client::events::UpdateClient;
use ibc_relayer_types::core::ics02_client::header::Header;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use ics12_proto::v1::Header as RawNearHeader;
use serde::{Deserialize, Serialize};

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
        now: C::Time,
    ) -> Result<Verified<C::Header>, error::Error>;

    /// Fetch a header from the chain at the given height and verify it.
    fn verify(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
        now: C::Time,
    ) -> Result<Verified<C::LightBlock>, error::Error>;

    /// Given a client update event that includes the header used in a client update,
    /// run the light client attack detector.
    fn detect_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
        now: C::Time,
    ) -> Result<Option<MisbehaviourEvidence>, error::Error>;

    /// Fetch a header from the chain at the given height, without verifying it
    fn fetch(&mut self, height: Height) -> Result<C::LightBlock, error::Error>;
}

/// Decodes an encoded header into a known `Header` type,
pub fn decode_header(header_bytes: &[u8]) -> Result<Box<dyn Header>, Error> {
    // For now, we only have tendermint; however when there is more than one, we
    // can try decoding into all the known types, and return an error only if
    // none work
    let header: TendermintHeader =
        ErasedProtobuf::<Any>::decode(header_bytes).map_err(Error::invalid_raw_header)?;

    Ok(Box::new(header))
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Tendermint(TendermintHeader),
    Near(NearHeader),
}

impl Header for AnyHeader {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(header) => header.client_type(),
            Self::Near(header) => header.client_type(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(header) => header.height(),
            Self::Near(header) => header.height(),
        }
    }

    fn timestamp(&self) -> Timestamp {
        match self {
            Self::Tendermint(header) => header.timestamp(),
            Self::Near(header) => header.timestamp(),
        }
    }
}

impl ErasedProtobuf<Any> for AnyHeader {}

impl TryFrom<Any> for AnyHeader {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Error> {
        match raw.type_url.as_str() {
            TENDERMINT_HEADER_TYPE_URL => {
                let val = tm_decode_header(raw.value.deref())?;

                Ok(AnyHeader::Tendermint(val))
            }
            NEAR_HEADER_TYPE_URL => {
                let val = near_decode_header(raw.value.deref())?;

                Ok(AnyHeader::Near(val))
            }

            _ => Err(Error::unknown_header_type(raw.type_url)),
        }
    }
}

impl From<AnyHeader> for Any {
    fn from(value: AnyHeader) -> Self {
        match value {
            AnyHeader::Tendermint(header) => Any {
                type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
                value: ErasedProtobuf::<RawTmHeader>::encode_vec(&header),
            },
            AnyHeader::Near(header) => Any {
                type_url: NEAR_HEADER_TYPE_URL.to_string(),
                value: ErasedProtobuf::<RawNearHeader>::encode_vec(&header),
            },
        }
    }
}

impl From<TendermintHeader> for AnyHeader {
    fn from(header: TendermintHeader) -> Self {
        Self::Tendermint(header)
    }
}

impl From<NearHeader> for AnyHeader {
    fn from(header: NearHeader) -> Self {
        Self::Near(header)
    }
}
