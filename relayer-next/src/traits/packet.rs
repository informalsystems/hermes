use crate::traits::chain_context::IbcChainContext;
use crate::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};

pub trait IbcPacket<SrcChain, DstChain>: Send
where
    SrcChain: IbcChainContext<DstChain>,
    DstChain: IbcChainContext<SrcChain>,
{
    fn source_port(&self) -> &PortId<SrcChain, DstChain>;

    fn source_channel_id(&self) -> &ChannelId<SrcChain, DstChain>;

    fn destination_port(&self) -> &PortId<DstChain, SrcChain>;

    fn destination_channel_id(&self) -> &ChannelId<DstChain, SrcChain>;

    fn sequence(&self) -> &Sequence<SrcChain, DstChain>;

    fn timeout_height(&self) -> Option<Height<DstChain>>;

    fn timeout_timestamp(&self) -> &Timestamp<DstChain>;
}
