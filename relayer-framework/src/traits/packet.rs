use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::types::aliases::{ChannelId, PortId, Sequence};

pub trait IbcPacket<SrcChain, DstChain>: Async
where
    SrcChain: IbcChainContext<DstChain>,
    DstChain: IbcChainContext<SrcChain>,
{
    fn source_port(&self) -> &PortId<SrcChain, DstChain>;

    fn source_channel_id(&self) -> &ChannelId<SrcChain, DstChain>;

    fn destination_port(&self) -> &PortId<DstChain, SrcChain>;

    fn destination_channel_id(&self) -> &ChannelId<DstChain, SrcChain>;

    fn sequence(&self) -> &Sequence<SrcChain, DstChain>;

    fn timeout_height(&self) -> Option<&DstChain::Height>;

    fn timeout_timestamp(&self) -> &DstChain::Timestamp;
}
