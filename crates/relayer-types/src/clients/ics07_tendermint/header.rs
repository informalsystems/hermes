use std::fmt::{Display, Error as FmtError, Formatter};

use bytes::Buf;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::lightclients::tendermint::v1::Header as RawHeader;
use ibc_proto::Protobuf;
use prost::Message;
use serde_derive::{Deserialize, Serialize};
use tendermint::block::signed_header::SignedHeader;
use tendermint::validator::Set as ValidatorSet;

use crate::clients::ics07_tendermint::error::Error;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics24_host::identifier::ChainId;
use crate::timestamp::Timestamp;
use crate::utils::pretty::{PrettySignedHeader, PrettyValidatorSet};
use crate::Height;

pub const TENDERMINT_HEADER_TYPE_URL: &str = "/ibc.lightclients.tendermint.v1.Header";

/// Tendermint consensus header
#[derive(Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct Header {
    pub signed_header: SignedHeader, // contains the commitment root
    pub validator_set: ValidatorSet, // the validator set that signed Header
    pub trusted_height: Height, // the height of a trusted header seen by client less than or equal to Header
    // TODO(thane): Rename this to trusted_next_validator_set?
    pub trusted_validator_set: ValidatorSet, // the last trusted validator set at trusted height
}

impl core::fmt::Debug for Header {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, " Header {{...}}")
    }
}

impl Display for Header {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "Header {{ signed_header: {}, validator_set: {}, trusted_height: {}, trusted_validator_set: {} }}", PrettySignedHeader(&self.signed_header), PrettyValidatorSet(&self.validator_set), self.trusted_height, PrettyValidatorSet(&self.trusted_validator_set))
    }
}

impl Header {
    pub fn height(&self) -> Height {
        Height::new(
            ChainId::chain_version(self.signed_header.header.chain_id.as_str()),
            u64::from(self.signed_header.header.height),
        )
        .expect("malformed tendermint header domain type has an illegal height of 0")
    }
}

impl crate::core::ics02_client::header::Header for Header {
    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn height(&self) -> Height {
        self.height()
    }

    fn timestamp(&self) -> Timestamp {
        self.signed_header.header.time.into()
    }
}

impl Protobuf<RawHeader> for Header {}

impl TryFrom<RawHeader> for Header {
    type Error = Error;

    fn try_from(raw: RawHeader) -> Result<Self, Self::Error> {
        let header = Self {
            signed_header: raw
                .signed_header
                .ok_or_else(Error::missing_signed_header)?
                .try_into()
                .map_err(|e| Error::invalid_header("signed header conversion".to_string(), e))?,
            validator_set: raw
                .validator_set
                .ok_or_else(Error::missing_validator_set)?
                .try_into()
                .map_err(Error::invalid_raw_header)?,
            trusted_height: raw
                .trusted_height
                .and_then(|raw_height| raw_height.try_into().ok())
                .ok_or_else(Error::missing_trusted_height)?,
            trusted_validator_set: raw
                .trusted_validators
                .ok_or_else(Error::missing_trusted_validator_set)?
                .try_into()
                .map_err(Error::invalid_raw_header)?,
        };

        if header.height().revision_number() != header.trusted_height.revision_number() {
            return Err(Error::mismatched_revisions(
                header.trusted_height.revision_number(),
                header.height().revision_number(),
            ));
        }

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
            TENDERMINT_HEADER_TYPE_URL => decode_header(raw.value.deref()).map_err(Into::into),
            _ => Err(Ics02Error::unknown_header_type(raw.type_url)),
        }
    }
}

impl From<Header> for Any {
    fn from(header: Header) -> Self {
        Any {
            type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
            value: Protobuf::<RawHeader>::encode_vec(header),
        }
    }
}

pub fn decode_header<B: Buf>(buf: B) -> Result<Header, Error> {
    RawHeader::decode(buf).map_err(Error::decode)?.try_into()
}

impl From<Header> for RawHeader {
    fn from(value: Header) -> Self {
        RawHeader {
            signed_header: Some(value.signed_header.into()),
            validator_set: Some(value.validator_set.into()),
            trusted_height: Some(value.trusted_height.into()),
            trusted_validators: Some(value.trusted_validator_set.into()),
        }
    }
}
