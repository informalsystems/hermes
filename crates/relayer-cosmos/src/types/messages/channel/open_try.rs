use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenTry as ProtoMsgChannelOpenTry;
use ibc_relayer_types::core::ics04_channel::channel::ChannelEnd;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc_relayer_types::core::ics24_host::identifier::PortId;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::methods::encode::encode_to_any;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelOpenTry";

#[derive(Debug)]
pub struct CosmosChannelOpenTryMessage {
    pub port_id: PortId,
    pub channel: ChannelEnd,
    pub counterparty_version: Version,
    pub update_height: Height,
    pub proof_init: CommitmentProofBytes,
}

impl CosmosMessage for CosmosChannelOpenTryMessage {
    fn counterparty_message_height_for_update_client(&self) -> Option<Height> {
        Some(self.update_height)
    }

    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        #[allow(deprecated)]
        let proto_message = ProtoMsgChannelOpenTry {
            port_id: self.port_id.to_string(),
            channel: Some(self.channel.clone().into()),
            counterparty_version: self.counterparty_version.to_string(),
            proof_height: Some(self.update_height.into()),
            proof_init: self.proof_init.clone().into(),
            signer: signer.to_string(),
            previous_channel_id: "".to_string(),
        };

        encode_to_any(TYPE_URL, &proto_message)
    }
}
