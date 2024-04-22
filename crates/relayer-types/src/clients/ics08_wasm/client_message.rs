use bytes::Buf;
use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};

use ibc_proto::ibc::lightclients::wasm::v1::ClientMessage as RawClientMessage;

use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::header::AnyHeader;
use crate::timestamp::Timestamp;

use super::error::Error;

pub const WASM_CLIENT_MESSAGE_TYPE_URL: &str = "/ibc.lightclients.wasm.v1.ClientMessage";

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct ClientMessage {
    pub data: Box<AnyHeader>,
}

impl crate::core::ics02_client::header::Header for ClientMessage {
    fn client_type(&self) -> ClientType {
        self.data.client_type()
    }

    fn height(&self) -> crate::Height {
        self.data.height()
    }

    fn timestamp(&self) -> Timestamp {
        self.data.timestamp()
    }
}

pub fn wasm_decode_client_message<B: Buf>(buf: B) -> Result<ClientMessage, Error> {
    RawClientMessage::decode(buf)
        .map_err(Error::proto_decode)?
        .try_into()
}

impl Protobuf<RawClientMessage> for ClientMessage {}

impl TryFrom<RawClientMessage> for ClientMessage {
    type Error = Error;

    fn try_from(value: RawClientMessage) -> Result<Self, Self::Error> {
        let any = Any::decode(value.data.as_slice()).map_err(Error::proto_decode)?;
        let data = AnyHeader::try_from(any)?;
        Ok(ClientMessage {
            data: Box::new(data),
        })
    }
}

impl From<ClientMessage> for RawClientMessage {
    fn from(value: ClientMessage) -> Self {
        RawClientMessage {
            data: Any::from(*value.data).encode_to_vec(),
        }
    }
}
