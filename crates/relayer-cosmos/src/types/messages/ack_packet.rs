use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::channel::v1::MsgAcknowledgement as ProtoMsgAcknowledgement;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::proofs::Proofs;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::methods::encode::encode_message;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.channel.v1.MsgAcknowledgement";

pub struct CosmosAckPacketMessage {
    pub packet: Packet,
    pub acknowledgement: Vec<u8>,
    pub proofs: Proofs,
    pub height: Height,
}

impl CosmosMessage for CosmosAckPacketMessage {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        Some(self.proofs.height())
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgAcknowledgement {
            packet: Some(self.packet.clone().into()),
            acknowledgement: self.acknowledgement.clone(),
            proof_acked: self.proofs.object_proof().clone().into(),
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
