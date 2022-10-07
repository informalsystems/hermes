use ibc_proto::{google::protobuf::Any, protobuf::Protobuf};
use ibc_relayer_types::clients::ics07_tendermint::misbehaviour::{
    Misbehaviour as TmMisbehaviour, TENDERMINT_MISBEHAVIOR_TYPE_URL,
};
use ibc_relayer_types::core::{
    ics02_client::{error::Error, misbehaviour::Misbehaviour},
    ics24_host::identifier::ClientId,
};
#[cfg(test)]
use ibc_relayer_types::mock::misbehaviour::Misbehaviour as MockMisbehaviour;
#[cfg(test)]
use ibc_relayer_types::mock::misbehaviour::MOCK_MISBEHAVIOUR_TYPE_URL;
use ibc_relayer_types::Height;
use serde::{Deserialize, Serialize};

use crate::light_client::AnyHeader;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MisbehaviourEvidence {
    pub misbehaviour: AnyMisbehaviour,
    pub supporting_headers: Vec<AnyHeader>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[allow(clippy::large_enum_variant)]
pub enum AnyMisbehaviour {
    Tendermint(TmMisbehaviour),

    #[cfg(test)]
    Mock(MockMisbehaviour),
}

impl Misbehaviour for AnyMisbehaviour {
    fn client_id(&self) -> &ClientId {
        match self {
            Self::Tendermint(misbehaviour) => misbehaviour.client_id(),

            #[cfg(test)]
            Self::Mock(misbehaviour) => misbehaviour.client_id(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(misbehaviour) => misbehaviour.height(),

            #[cfg(test)]
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

            #[cfg(test)]
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

            #[cfg(test)]
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

            #[cfg(test)]
            AnyMisbehaviour::Mock(mock) => write!(f, "{:?}", mock),
        }
    }
}

impl From<TmMisbehaviour> for AnyMisbehaviour {
    fn from(misbehaviour: TmMisbehaviour) -> Self {
        Self::Tendermint(misbehaviour)
    }
}

#[cfg(test)]
impl From<MockMisbehaviour> for AnyMisbehaviour {
    fn from(misbehaviour: MockMisbehaviour) -> Self {
        Self::Mock(misbehaviour)
    }
}
