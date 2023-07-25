use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as ProtoMsgChannelOpenInit;
use ibc_relayer_types::core::ics04_channel::channel::ChannelEnd;
use ibc_relayer_types::core::ics24_host::identifier::PortId;
use ibc_relayer_types::signer::Signer;
use prost::EncodeError;

use crate::methods::encode::encode_message;
use crate::traits::message::CosmosMessage;

const TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelOpenInit";

pub struct CosmosChannelOpenInitMessage {
    pub port_id: PortId,
    pub channel: ChannelEnd,
}

impl CosmosMessage for CosmosChannelOpenInitMessage {
    fn encode_protobuf(&self, signer: &Signer) -> Result<Any, EncodeError> {
        let proto_message = ProtoMsgChannelOpenInit {
            port_id: self.port_id.to_string(),
            channel: Some(self.channel.clone().into()),
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
