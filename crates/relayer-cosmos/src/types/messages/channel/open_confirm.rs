use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenConfirm as ProtoMsgChannelOpenConfirm;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::methods::encode::encode_to_any;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelOpenConfirm";

#[derive(Debug)]
pub struct CosmosChannelOpenConfirmMessage {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub update_height: Height,
    pub proof_ack: CommitmentProofBytes,
}

impl CosmosMessage for CosmosChannelOpenConfirmMessage {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        Some(self.update_height)
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgChannelOpenConfirm {
            port_id: self.port_id.to_string(),
            channel_id: self.channel_id.to_string(),
            proof_height: Some(self.update_height.into()),
            proof_ack: self.proof_ack.clone().into(),
            signer: signer.to_string(),
        };

        encode_to_any(TYPE_URL, &proto_message)
    }
}
