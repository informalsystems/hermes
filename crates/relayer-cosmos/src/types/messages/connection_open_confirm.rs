use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenConfirm as ProtoMsgConnectionOpenConfirm;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
use ibc_relayer_types::proofs::Proofs;
use ibc_relayer_types::signer::Signer;
use prost::EncodeError;

use crate::methods::encode::encode_message;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.connection.v1.MsgConnectionOpenConfirm";

pub struct CosmosConnectionOpenConfirmMessage {
    pub connection_id: ConnectionId,
    pub proofs: Proofs,
}

impl CosmosMessage for CosmosConnectionOpenConfirmMessage {
    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgConnectionOpenConfirm {
            connection_id: self.connection_id.as_str().to_string(),
            proof_height: Some(self.proofs.height().into()),
            proof_ack: self.proofs.object_proof().clone().into(),
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
