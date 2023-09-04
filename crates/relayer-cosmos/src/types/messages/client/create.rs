use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::MsgCreateClient as ProtoMsgCreateClient;
use ibc_relayer_types::signer::Signer;
use prost::EncodeError;

use crate::methods::encode::encode_to_any;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.client.v1.MsgCreateClient";

#[derive(Debug)]
pub struct CosmosCreateClientMessage {
    pub client_state: Any,
    pub consensus_state: Any,
}

impl CosmosMessage for CosmosCreateClientMessage {
    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgCreateClient {
            client_state: Some(self.client_state.clone()),
            consensus_state: Some(self.consensus_state.clone()),
            signer: signer.to_string(),
        };

        encode_to_any(TYPE_URL, &proto_message)
    }
}
