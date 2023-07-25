use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::channel::v1::MsgTimeout as ProtoMsgTimeout;
use ibc_relayer_types::core::ics04_channel::packet::{Packet, Sequence};
use ibc_relayer_types::proofs::Proofs;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::methods::encode::encode_message;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.channel.v1.MsgTimeout";

pub struct CosmosTimeoutPacketMessage {
    pub packet: Packet,
    pub next_sequence_recv: Sequence,
    pub proofs: Proofs,
    pub height: Height,
}

impl CosmosMessage for CosmosTimeoutPacketMessage {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        Some(self.proofs.height())
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgTimeout {
            packet: Some(self.packet.clone().into()),
            next_sequence_recv: self.next_sequence_recv.into(),
            proof_unreceived: self.proofs.object_proof().clone().into(),
            proof_height: Some(self.proofs.height().into()),
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
