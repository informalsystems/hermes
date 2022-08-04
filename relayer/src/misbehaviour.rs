use ibc::clients::ics07_tendermint::misbehaviour::Misbehaviour as TmMisbehaviour;
use ibc::core::{
    ics02_client::{
        error::Error,
        misbehaviour::{Misbehaviour, MOCK_MISBEHAVIOUR_TYPE_URL, TENDERMINT_MISBEHAVIOR_TYPE_URL},
    },
    ics24_host::identifier::ClientId,
};
use ibc::mock::misbehaviour::Misbehaviour as MockMisbehaviour;
use ibc::Height;
use ibc_proto::{google::protobuf::Any, protobuf::Protobuf};

use crate::light_client::AnyHeader;

#[derive(Clone, Debug, PartialEq)]
pub struct MisbehaviourEvidence {
    pub misbehaviour: AnyMisbehaviour,
    pub supporting_headers: Vec<AnyHeader>,
}

#[derive(Clone, Debug, PartialEq)] // TODO: Add Eq bound once possible
#[allow(clippy::large_enum_variant)]
pub enum AnyMisbehaviour {
    Tendermint(TmMisbehaviour),

    Mock(MockMisbehaviour),
}

impl Misbehaviour for AnyMisbehaviour {
    fn client_id(&self) -> &ClientId {
        match self {
            Self::Tendermint(misbehaviour) => misbehaviour.client_id(),

            Self::Mock(misbehaviour) => misbehaviour.client_id(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(misbehaviour) => misbehaviour.height(),

            Self::Mock(misbehaviour) => misbehaviour.height(),
        }
    }
}

impl Protobuf<Any> for AnyMisbehaviour {}

impl TryFrom<Any> for AnyMisbehaviour {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Error> {
        match raw.type_url.as_str() {
            TENDERMINT_MISBEHAVIOR_TYPE_URL => Ok(AnyMisbehaviour::Tendermint(
                TmMisbehaviour::decode_vec(&raw.value).map_err(Error::decode_raw_misbehaviour)?,
            )),

            MOCK_MISBEHAVIOUR_TYPE_URL => Ok(AnyMisbehaviour::Mock(
                MockMisbehaviour::decode_vec(&raw.value).map_err(Error::decode_raw_misbehaviour)?,
            )),
            _ => Err(Error::unknown_misbehaviour_type(raw.type_url)),
        }
    }
}

impl From<AnyMisbehaviour> for Any {
    fn from(value: AnyMisbehaviour) -> Self {
        match value {
            AnyMisbehaviour::Tendermint(misbehaviour) => Any {
                type_url: TENDERMINT_MISBEHAVIOR_TYPE_URL.to_string(),
                value: misbehaviour
                    .encode_vec()
                    .expect("encoding to `Any` from `AnyMisbehavior::Tendermint`"),
            },

            AnyMisbehaviour::Mock(misbehaviour) => Any {
                type_url: MOCK_MISBEHAVIOUR_TYPE_URL.to_string(),
                value: misbehaviour
                    .encode_vec()
                    .expect("encoding to `Any` from `AnyMisbehavior::Mock`"),
            },
        }
    }
}

impl core::fmt::Display for AnyMisbehaviour {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        match self {
            AnyMisbehaviour::Tendermint(tm) => write!(f, "{}", tm),

            AnyMisbehaviour::Mock(mock) => write!(f, "{:?}", mock),
        }
    }
}

impl From<MockMisbehaviour> for AnyMisbehaviour {
    fn from(misbehaviour: MockMisbehaviour) -> Self {
        Self::Mock(misbehaviour)
    }
}

impl From<TmMisbehaviour> for AnyMisbehaviour {
    fn from(misbehaviour: TmMisbehaviour) -> Self {
        Self::Tendermint(misbehaviour)
    }
}
