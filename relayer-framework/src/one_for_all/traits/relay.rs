use async_trait::async_trait;

use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::components::chain::OfaChainComponents;
use crate::one_for_all::traits::error::OfaError;
use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::std_prelude::*;
use crate::traits::core::Async;

#[async_trait]
pub trait OfaRelay: Async {
    type Components: OfaChainComponents<Self::SrcChain> + OfaChainComponents<Self::DstChain>;

    type Error: OfaError;

    type Runtime: OfaRuntime<Error = Self::Error>;

    type SrcChain: OfaChain<
        Error = Self::Error,
        Runtime = Self::Runtime,
        Components = Self::Components,
        CounterpartyHeight = <Self::DstChain as OfaChain>::Height,
        CounterpartySequence = <Self::DstChain as OfaChain>::Sequence,
        CounterpartyConsensusState = <Self::DstChain as OfaChain>::ConsensusState,
    >;

    type DstChain: OfaChain<
        Error = Self::Error,
        Runtime = Self::Runtime,
        Components = Self::Components,
        CounterpartyHeight = <Self::SrcChain as OfaChain>::Height,
        CounterpartySequence = <Self::SrcChain as OfaChain>::Sequence,
        CounterpartyConsensusState = <Self::SrcChain as OfaChain>::ConsensusState,
    >;

    type Packet: Async;

    fn packet_src_port(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::PortId;

    fn packet_src_channel_id(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::ChannelId;

    fn packet_dst_port(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::PortId;

    fn packet_dst_channel_id(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::ChannelId;

    fn packet_sequence(packet: &Self::Packet) -> &<Self::SrcChain as OfaChain>::Sequence;

    fn packet_timeout_height(
        packet: &Self::Packet,
    ) -> Option<&<Self::DstChain as OfaChain>::Height>;

    fn packet_timeout_timestamp(packet: &Self::Packet) -> &<Self::DstChain as OfaChain>::Timestamp;

    fn src_client_id(&self) -> &<Self::SrcChain as OfaChain>::ClientId;

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChain>::ClientId;

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaChain>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaChain>::Message>, Self::Error>;

    async fn build_dst_update_client_messages(
        &self,
        height: &<Self::SrcChain as OfaChain>::Height,
    ) -> Result<Vec<<Self::DstChain as OfaChain>::Message>, Self::Error>;

    async fn build_receive_packet_message(
        &self,
        height: &<Self::SrcChain as OfaChain>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::DstChain as OfaChain>::Message, Self::Error>;

    async fn build_ack_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChain>::Height,
        packet: &Self::Packet,
        ack: &<Self::DstChain as OfaChain>::WriteAcknowledgementEvent,
    ) -> Result<<Self::SrcChain as OfaChain>::Message, Self::Error>;
}
