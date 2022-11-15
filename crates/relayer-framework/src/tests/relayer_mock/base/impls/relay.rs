use alloc::boxed::Box;
use alloc::string::ToString;
use alloc::vec::Vec;
use async_trait::async_trait;
use std::vec;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayTypes};
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::common::one_for_all::presets::MinimalPreset;
use crate::common::one_for_all::types::chain::OfaChainWrapper;
use crate::tests::relayer_mock::base::error::Error;
use crate::tests::relayer_mock::base::types::message::Message as MockMessage;
use crate::tests::relayer_mock::base::types::packet::PacketKey;
use crate::tests::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::tests::relayer_mock::contexts::chain::MockChainContext;
use crate::tests::relayer_mock::contexts::relay::MockRelayContext;

impl OfaRelayTypes for MockRelayContext {
    type Preset = MinimalPreset;

    type Error = Error;

    type Runtime = MockRuntimeContext;

    type Packet = PacketKey;

    type SrcChain = MockChainContext;

    type DstChain = MockChainContext;
}

#[async_trait]
impl OfaBaseRelay for MockRelayContext {
    fn mismatch_ibc_events_count_error(expected: usize, actual: usize) -> Self::Error {
        Error::mismatch_error(expected, actual)
    }

    fn packet_src_channel_id(
        packet: &Self::Packet,
    ) -> &<Self::SrcChain as OfaChainTypes>::ChannelId {
        &packet.channel_id
    }

    fn packet_src_port(packet: &Self::Packet) -> &<Self::SrcChain as OfaChainTypes>::PortId {
        &packet.channel_id
    }

    fn packet_dst_port(packet: &Self::Packet) -> &<Self::DstChain as OfaChainTypes>::PortId {
        &packet.port_id
    }

    fn packet_dst_channel_id(
        packet: &Self::Packet,
    ) -> &<Self::DstChain as OfaChainTypes>::ChannelId {
        &packet.channel_id
    }

    fn packet_sequence(packet: &Self::Packet) -> &<Self::SrcChain as OfaChainTypes>::Sequence {
        &packet.sequence
    }

    fn packet_timeout_height(
        packet: &Self::Packet,
    ) -> Option<&<Self::DstChain as OfaChainTypes>::Height> {
        Some(&packet.timeout_height)
    }

    fn packet_timeout_timestamp(
        packet: &Self::Packet,
    ) -> &<Self::DstChain as OfaChainTypes>::Timestamp {
        &packet.timeout_timestamp
    }

    fn runtime(&self) -> &OfaRuntimeContext<Self::Runtime> {
        &self.runtime
    }

    fn src_client_id(&self) -> &<Self::SrcChain as OfaChainTypes>::ClientId {
        self.src_to_dst_client()
    }

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChainTypes>::ClientId {
        self.dst_to_src_client()
    }

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain> {
        &self.dst_chain
    }

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaChainTypes>::Message>, Self::Error> {
        let state = self.src_chain().chain.state();
        Ok(vec![MockMessage::UpdateClient(
            self.src_client_id().to_string(),
            height.clone(),
            state,
        )])
    }

    async fn build_dst_update_client_messages(
        &self,
        height: &<Self::SrcChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::DstChain as OfaChainTypes>::Message>, Self::Error> {
        let state = self.dst_chain().chain.state();
        Ok(vec![MockMessage::UpdateClient(
            self.dst_client_id().to_string(),
            height.clone(),
            state,
        )])
    }

    async fn build_receive_packet_message(
        &self,
        height: &<Self::SrcChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::DstChain as OfaChainTypes>::Message, Self::Error> {
        let h = self.dst_chain().chain.get_latest_height().unwrap();
        Ok(MockMessage::SendPacket(
            packet.client_id.clone(),
            height.clone(),
            h,
            packet.clone(),
        ))
    }

    async fn build_ack_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
        _ack: &<Self::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error> {
        Ok(MockMessage::AckPacket(
            self.src_client_id().clone(),
            destination_height.clone(),
            packet.clone(),
        ))
    }

    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error> {
        Ok(MockMessage::TimeoutPacket(
            self.src_client_id().clone(),
            destination_height.clone(),
            packet.clone(),
        ))
    }
}
