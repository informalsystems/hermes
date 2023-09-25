use core::time::Duration;

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::commitment::v1::MerklePrefix;
use ibc_proto::ibc::core::connection::v1::Counterparty;
use ibc_proto::ibc::core::connection::v1::MsgConnectionOpenTry as ProtoMsgConnectionOpenTry;
use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::core::ics24_host::identifier::{ClientId, ConnectionId};
use ibc_relayer_types::proofs::ConsensusProof;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::methods::encode::encode_to_any;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.connection.v1.MsgConnectionOpenTry";

pub struct CosmosConnectionOpenTryMessage {
    pub client_id: ClientId,
    pub counterparty_client_id: ClientId,
    pub counterparty_connection_id: ConnectionId,
    pub counterparty_commitment_prefix: CommitmentPrefix,
    pub counterparty_versions: Vec<Version>,
    pub client_state: Any,
    pub delay_period: Duration,
    pub update_height: Height,
    pub proof_init: CommitmentProofBytes,
    pub proof_client: CommitmentProofBytes,
    pub proof_consensus: ConsensusProof,
}

impl CosmosMessage for CosmosConnectionOpenTryMessage {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        Some(self.update_height)
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let counterparty = Counterparty {
            client_id: self.counterparty_client_id.as_str().to_string(),
            prefix: Some(MerklePrefix {
                key_prefix: self.counterparty_commitment_prefix.clone().into_vec(),
            }),
            connection_id: self.counterparty_connection_id.as_str().to_string(),
        };

        #[allow(deprecated)]
        let proto_message = ProtoMsgConnectionOpenTry {
            client_id: self.client_id.as_str().to_string(),
            counterparty: Some(counterparty),
            counterparty_versions: self
                .counterparty_versions
                .iter()
                .map(|v| v.clone().into())
                .collect(),
            client_state: Some(self.client_state.clone()),
            delay_period: self.delay_period.as_nanos() as u64,
            proof_height: Some(self.update_height.into()),
            proof_init: self.proof_init.clone().into(),
            proof_client: self.proof_client.clone().into(),
            proof_consensus: self.proof_consensus.proof().clone().into(),
            consensus_height: Some(self.proof_consensus.height().into()),
            signer: signer.to_string(),
            previous_connection_id: "".to_string(),
            host_consensus_state_proof: Vec::new(),
        };

        encode_to_any(TYPE_URL, &proto_message)
    }
}
