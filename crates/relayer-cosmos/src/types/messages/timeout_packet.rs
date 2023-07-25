use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::channel::v1::MsgTimeout as ProtoMsgTimeout;
use ibc_relayer_types::core::ics04_channel::packet::{Packet, Sequence};
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::methods::encode::encode_message;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.channel.v1.MsgTimeout";

pub struct CosmosTimeoutPacketMessage {
    pub packet: Packet,
    pub next_sequence_recv: Sequence,
    pub update_height: Height,
    pub proof_unreceived: CommitmentProofBytes,
}

impl CosmosMessage for CosmosTimeoutPacketMessage {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        Some(self.update_height)
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgTimeout {
            packet: Some(self.packet.clone().into()),
            next_sequence_recv: self.next_sequence_recv.into(),
            proof_unreceived: self.proof_unreceived.clone().into(),
            proof_height: Some(self.update_height.into()),
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
