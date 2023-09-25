use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenAck as ProtoMsgConnectionOpenAck;
use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
use ibc_relayer_types::proofs::ConsensusProof;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::methods::encode::encode_to_any;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.connection.v1.MsgConnectionOpenAck";

pub struct CosmosConnectionOpenAckMessage {
    pub connection_id: ConnectionId,
    pub counterparty_connection_id: ConnectionId,
    pub version: Version,
    pub client_state: Any,
    pub update_height: Height,
    pub proof_try: CommitmentProofBytes,
    pub proof_client: CommitmentProofBytes,
    pub proof_consensus: ConsensusProof,
}

impl CosmosMessage for CosmosConnectionOpenAckMessage {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        Some(self.update_height)
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgConnectionOpenAck {
            connection_id: self.connection_id.as_str().to_string(),
            counterparty_connection_id: self.counterparty_connection_id.as_str().to_string(),
            client_state: Some(self.client_state.clone()),
            proof_height: Some(self.update_height.into()),
            proof_try: self.proof_try.clone().into(),
            proof_client: self.proof_client.clone().into(),
            proof_consensus: self.proof_consensus.proof().clone().into(),
            consensus_height: Some(self.proof_consensus.height().into()),
            version: Some(self.version.clone().into()),
            signer: signer.to_string(),
            host_consensus_state_proof: Vec::new(),
        };

        encode_to_any(TYPE_URL, &proto_message)
    }
}
