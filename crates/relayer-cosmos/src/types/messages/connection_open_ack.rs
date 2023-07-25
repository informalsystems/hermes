use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenAck as ProtoMsgConnectionOpenAck;
use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
use ibc_relayer_types::proofs::Proofs;
use ibc_relayer_types::signer::Signer;
use prost::EncodeError;

use crate::methods::encode::encode_message;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.connection.v1.MsgConnectionOpenAck";

pub struct CosmosConnectionOpenAckMessage {
    pub connection_id: ConnectionId,
    pub counterparty_connection_id: ConnectionId,
    pub version: Version,
    pub client_state: Any,
    pub proofs: Proofs,
}

impl CosmosMessage for CosmosConnectionOpenAckMessage {
    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgConnectionOpenAck {
            connection_id: self.connection_id.as_str().to_string(),
            counterparty_connection_id: self.counterparty_connection_id.as_str().to_string(),
            client_state: Some(self.client_state.clone()),
            proof_height: Some(self.proofs.height().into()),
            proof_try: self.proofs.object_proof().clone().into(),
            proof_client: self
                .proofs
                .client_proof()
                .clone()
                .map(Into::into)
                .unwrap_or_default(),
            proof_consensus: self
                .proofs
                .consensus_proof()
                .map(|p| p.proof().clone().into())
                .unwrap_or_default(),
            consensus_height: self
                .proofs
                .consensus_proof()
                .map(|p| Some(p.height().into()))
                .unwrap_or_default(),
            version: Some(self.version.clone().into()),
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
