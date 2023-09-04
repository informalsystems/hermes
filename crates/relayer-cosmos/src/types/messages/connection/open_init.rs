use core::time::Duration;

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::commitment::v1::MerklePrefix;
use ibc_proto::ibc::core::connection::v1::{
    Counterparty, MsgConnectionOpenInit as ProtoMsgConnectionOpenInit,
};
use ibc_relayer_types::core::ics03_connection::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentPrefix;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::signer::Signer;
use prost::EncodeError;

use crate::methods::encode::encode_to_any;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.connection.v1.MsgConnectionOpenInit";

#[derive(Debug)]
pub struct CosmosConnectionOpenInitMessage {
    pub client_id: ClientId,
    pub counterparty_client_id: ClientId,
    pub counterparty_commitment_prefix: CommitmentPrefix,
    pub version: Version,
    pub delay_period: Duration,
}

impl CosmosMessage for CosmosConnectionOpenInitMessage {
    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let counterparty = Counterparty {
            client_id: self.counterparty_client_id.as_str().to_string(),
            prefix: Some(MerklePrefix {
                key_prefix: self.counterparty_commitment_prefix.clone().into_vec(),
            }),
            connection_id: "".to_string(),
        };

        let proto_message = ProtoMsgConnectionOpenInit {
            client_id: self.client_id.as_str().to_string(),
            counterparty: Some(counterparty),
            version: Some(self.version.clone().into()),
            delay_period: self.delay_period.as_nanos() as u64,
            signer: signer.to_string(),
        };

        encode_to_any(TYPE_URL, &proto_message)
    }
}
