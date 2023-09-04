use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::channel::v1::MsgRecvPacket as ProtoMsgRecvPacket;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::methods::encode::encode_to_any;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.channel.v1.MsgRecvPacket";

#[derive(Debug)]
pub struct CosmosReceivePacketMessage {
    pub packet: Packet,
    pub update_height: Height,
    pub proof_commitment: CommitmentProofBytes,
}

impl CosmosMessage for CosmosReceivePacketMessage {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        Some(self.update_height)
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgRecvPacket {
            packet: Some(self.packet.clone().into()),
            proof_commitment: self.proof_commitment.clone().into(),
            proof_height: Some(self.update_height.into()),
            signer: signer.to_string(),
        };

        encode_to_any(TYPE_URL, &proto_message)
    }
}
