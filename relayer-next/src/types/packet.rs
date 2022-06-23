use crate::traits::chain_context::IbcChainContext;
use crate::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};

#[derive(Clone, Debug)]
pub struct Packet<SrcChain: IbcChainContext<DstChain>, DstChain: IbcChainContext<SrcChain>> {
    pub source_port: PortId<SrcChain, DstChain>,
    pub source_channel_id: ChannelId<SrcChain, DstChain>,
    pub destination_port: PortId<DstChain, SrcChain>,
    pub destination_channel_id: ChannelId<DstChain, SrcChain>,
    pub sequence: Sequence<SrcChain, DstChain>,
    pub timeout_height: Option<Height<DstChain>>,
    pub timeout_timestamp: Option<Timestamp<DstChain>>,
}
