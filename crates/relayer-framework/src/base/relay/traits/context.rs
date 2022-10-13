use crate::base::chain::traits::context::HasIbcChainTypes;
use crate::base::chain::types::aliases::{
    ChannelId, ClientId, Height, PortId, Sequence, Timestamp,
};
use crate::base::core::traits::error::HasError;
use crate::base::core::traits::sync::Async;

pub trait HasRelayTypes: HasError {
    type SrcChain: HasIbcChainTypes<Self::DstChain, Error = Self::Error>;

    type DstChain: HasIbcChainTypes<Self::SrcChain, Error = Self::Error>;

    type Packet: Async;

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
