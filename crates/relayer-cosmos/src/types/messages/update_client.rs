use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as ProtoMsgUpdateClient;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::signer::Signer;
use prost::EncodeError;

use crate::methods::encode::encode_message;
use crate::traits::message::CosmosMessage;

pub const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpdateClient";

pub struct CosmosUpdateClientMessage {
    pub client_id: ClientId,
    pub header: Any,
}

impl CosmosMessage for CosmosUpdateClientMessage {
    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgUpdateClient {
            client_id: self.client_id.to_string(),
            header: Some(self.header.clone()),
            signer: signer.to_string(),
        };

        let encoded_message = encode_message(&proto_message)?;

        let any_message = Any {
            type_url: TYPE_URL.to_string(),
            value: encoded_message,
        };

        Ok(any_message)
    }
}
