use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::chain::types::aliases::{
    ChannelId, ClientId, Height, PortId, Sequence, Timestamp,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;

pub trait HasRelayTypes: HasErrorType {
    type SrcChain: HasIbcChainTypes<Self::DstChain>;

    type DstChain: HasIbcChainTypes<Self::SrcChain>;

    type Packet: Async;

    fn src_chain_error(e: <Self::SrcChain as HasErrorType>::Error) -> Self::Error;

    fn dst_chain_error(e: <Self::DstChain as HasErrorType>::Error) -> Self::Error;

    fn packet_src_port(packet: &Self::Packet) -> &PortId<Self::SrcChain, Self::DstChain>;

    fn packet_src_channel_id(packet: &Self::Packet) -> &ChannelId<Self::SrcChain, Self::DstChain>;

    fn packet_dst_port(packet: &Self::Packet) -> &PortId<Self::DstChain, Self::SrcChain>;

    fn packet_dst_channel_id(packet: &Self::Packet) -> &ChannelId<Self::DstChain, Self::SrcChain>;

    fn packet_sequence(packet: &Self::Packet) -> &Sequence<Self::SrcChain, Self::DstChain>;

    fn packet_timeout_height(packet: &Self::Packet) -> Option<&Height<Self::DstChain>>;

    fn packet_timeout_timestamp(packet: &Self::Packet) -> &Timestamp<Self::DstChain>;

    fn source_chain(&self) -> &Self::SrcChain;

    fn destination_chain(&self) -> &Self::DstChain;

    fn source_client_id(&self) -> &ClientId<Self::SrcChain, Self::DstChain>;

    fn destination_client_id(&self) -> &ClientId<Self::DstChain, Self::SrcChain>;
}
