use std::convert::TryFrom;

use prost_types::Any;
use tendermint_proto::Protobuf;

use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::{Error, Kind};
use crate::ics07_tendermint::header::Header as TendermintHeader;
#[cfg(any(test, feature = "mocks"))]
use crate::mock::header::MockHeader;
use crate::Height;
use serde_derive::{Deserialize, Serialize};

pub const TENDERMINT_HEADER_TYPE_URL: &str = "/ibc.lightclients.tendermint.v1.Header";

#[cfg(any(test, feature = "mocks"))]
pub const MOCK_HEADER_TYPE_URL: &str = "/ibc.mock.Header";

/// Abstract of consensus state update information
#[dyn_clonable::clonable]
pub trait Header: Clone + std::fmt::Debug + Send + Sync {
    /// The type of client (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// The height of the consensus state
    fn height(&self) -> Height;

    /// Wrap into an `AnyHeader`
    fn wrap_any(self) -> AnyHeader;
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)] // TODO: Add Eq bound once possible
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Tendermint(TendermintHeader),

    #[cfg(any(test, feature = "mocks"))]
    Mock(MockHeader),
}

impl Header for AnyHeader {
    fn client_type(&self) -> ClientType {
        match self {
            Self::Tendermint(header) => header.client_type(),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(header) => header.client_type(),
        }
    }

    fn height(&self) -> Height {
        match self {
            Self::Tendermint(header) => header.height(),

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(header) => header.height(),
        }
    }

    fn wrap_any(self) -> AnyHeader {
        self
    }
}

impl Protobuf<Any> for AnyHeader {}

impl TryFrom<Any> for AnyHeader {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            TENDERMINT_HEADER_TYPE_URL => Ok(AnyHeader::Tendermint(
                TendermintHeader::decode_vec(&raw.value)
                    .map_err(|e| Kind::InvalidRawHeader.context(e))?,
            )),

            #[cfg(any(test, feature = "mocks"))]
            MOCK_HEADER_TYPE_URL => Ok(AnyHeader::Mock(
                MockHeader::decode_vec(&raw.value)
                    .map_err(|e| Kind::InvalidRawHeader.context(e))?,
            )),

            _ => Err(Kind::UnknownHeaderType(raw.type_url).into()),
        }
    }
}

impl From<AnyHeader> for Any {
    fn from(value: AnyHeader) -> Self {
        match value {
            AnyHeader::Tendermint(header) => Any {
                type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
                value: header.encode_vec().unwrap(),
            },
            #[cfg(any(test, feature = "mocks"))]
            AnyHeader::Mock(header) => Any {
                type_url: MOCK_HEADER_TYPE_URL.to_string(),
                value: header.encode_vec().unwrap(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ics02_client::client_header::AnyHeader;
    use subtle_encoding::hex;
    use tendermint_proto::Protobuf;

    #[test]
    fn header_event_deserialization() {
        let header: String = "0a262f6962632e6c69676874636c69656e74732e74656e6465726d696e742e76312e48656164657212df060ac8040a8b030a02080b12056962632d31188702220b08b1e8f9810610b8efdd702a480a208a07230bff1273f52dea8bdddc4426ac233e426a344d4cd35a3cbb6421ecffc8122408011220818cead2dd3001745fc966a5957a61bf052be9fe2b8028c1514298bc846963ab322065bae3ff941faf014d3a7d919a9d95462b98a684e8726bdd76c8d3fa190ba14e3a20e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b8554220c694926664a47cb04cd3c701bc739f5debb22d19d6b62d122ea52791b039540a4a20c694926664a47cb04cd3c701bc739f5debb22d19d6b62d122ea52791b039540a5220048091bc7ddc283f77bfbf91d73c44da58c3df8a9cbc867405d8b7f3daada22f5a2065b84d4af60c5e63201ab074bdc341382bb9ae6d356ae5c82bba1ffced9c326a6220e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b8556a20e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b8557214504e435ade1edf7f93f8a74dd5ea8f433088882c12b7010887021a480a20ab01dc644cac63878152d234520092833821acff43a73841a4e139089921fec1122408011220a8529fc7fcc11abbc001bf3af9f5c24e0b5b360e6d2ceb5c7201757969b2566f226808021214504e435ade1edf7f93f8a74dd5ea8f433088882c1a0c08b2e8f9810610d8c8c48e01224073f7f13bfe7a4f3a28405c21c7713e4f7a5ec83e3d73cfc89b35c29957292a905e2339b4a9fc2cb9bdc2c366837a2ed8bc2e329e463b66ec49c0ecd46d6765011284010a3e0a14504e435ade1edf7f93f8a74dd5ea8f433088882c12220a20c42ea9df299950d361120972c0ccf57d33afd387171a865093087c9f0835c2f418a08d06123e0a14504e435ade1edf7f93f8a74dd5ea8f433088882c12220a20c42ea9df299950d361120972c0ccf57d33afd387171a865093087c9f0835c2f418a08d0618a08d061a04080110182284010a3e0a14504e435ade1edf7f93f8a74dd5ea8f433088882c12220a20c42ea9df299950d361120972c0ccf57d33afd387171a865093087c9f0835c2f418a08d06123e0a14504e435ade1edf7f93f8a74dd5ea8f433088882c12220a20c42ea9df299950d361120972c0ccf57d33afd387171a865093087c9f0835c2f418a08d0618a08d06".to_string();
        let header_bytes = hex::decode(header).unwrap();

        let any_header: AnyHeader = Protobuf::decode(header_bytes.as_ref()).unwrap();
        println!("header {:?}", any_header);
    }
}
