use ibc::signer::Signer;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use prost::EncodeError;

use crate::tagged::{DualTagged, MonoTagged};

pub struct Message<DstChain, SrcChain> {
    pub source_height: Option<MonoTagged<SrcChain, Height>>,

    pub to_protobuf_fn: Box<
        dyn FnOnce(
                MonoTagged<DstChain, Signer>,
            ) -> Result<DualTagged<DstChain, SrcChain, Any>, EncodeError>
            + 'static
            + Send
            + Sync,
    >,
}

impl<DstChain, SrcChain> Message<DstChain, SrcChain> {
    pub fn to_protobuf(
        self,
        signer: MonoTagged<DstChain, Signer>,
    ) -> Result<DualTagged<DstChain, SrcChain, Any>, EncodeError> {
        (self.to_protobuf_fn)(signer)
    }
}

pub fn create_message<DstChain, SrcChain>(
    source_height: Option<MonoTagged<SrcChain, Height>>,
    to_protobuf: impl FnOnce(
            MonoTagged<DstChain, Signer>,
        ) -> Result<DualTagged<DstChain, SrcChain, Any>, EncodeError>
        + 'static
        + Send
        + Sync,
) -> Message<DstChain, SrcChain> {
    Message {
        source_height,
        to_protobuf_fn: Box::new(to_protobuf),
    }
}
