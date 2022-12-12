use alloc::boxed::Box;
use alloc::string::ToString;
use alloc::vec::Vec;
use async_trait::async_trait;
use std::vec;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::message::Message as MockMessage;
use crate::relayer_mock::base::types::packet::PacketKey;
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;
use crate::relayer_mock::contexts::relay::MockRelayContext;

use ibc_relayer_framework::base::one_for_all::traits::chain::OfaChainTypes;
use ibc_relayer_framework::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayTypes};
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::common::one_for_all::presets::MinimalPreset;
use ibc_relayer_framework::common::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_runtime::tokio::error::Error as TokioError;

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
    fn runtime_error(e: TokioError) -> Self::Error {
        Error::tokio(e)
    }

    fn src_chain_error(e: Error) -> Self::Error {
        e
    }

    fn dst_chain_error(e: Error) -> Self::Error {
        e
    }

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
        self.dst_to_src_client()
    }

    fn src_chain(&self) -> &OfaChainWrapper<Self::SrcChain> {
        &self.src_chain
    }

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChainTypes>::ClientId {
        self.src_to_dst_client()
    }

    fn dst_chain(&self) -> &OfaChainWrapper<Self::DstChain> {
        &self.dst_chain
    }

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaChainTypes>::Message>, Self::Error> {
        let state = self
            .dst_chain()
            .chain
            .query_state_at_height(height.clone())?;
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
        let state = self
            .src_chain()
            .chain
            .query_state_at_height(height.clone())?;
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
        // If the latest state of the source chain doesn't have the packet as sent, return an error.
        let state = self.src_chain().chain.get_current_state()?;
        if !state.check_sent(&packet.port_id, &packet.channel_id, &packet.sequence) {
            return Err(Error::receive_without_sent(
                self.src_chain().chain.name().to_string(),
                self.dst_chain().chain.name().to_string(),
            ));
        }
        Ok(MockMessage::RecvPacket(
            self.dst_client_id().clone(),
            height.clone(),
            packet.clone(),
        ))
    }

    async fn build_ack_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
        _ack: &<Self::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error> {
        let state = self.dst_chain().chain.get_current_state()?;
        // If the latest state of the destination chain doesn't have the packet as received, return an error.
        if !state.check_received(&packet.port_id, &packet.channel_id, &packet.sequence) {
            return Err(Error::acknowledgment_without_received(
                self.src_chain().chain.name().to_string(),
                self.dst_chain().chain.name().to_string(),
            ));
        }
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
        // If the latest state of the source chain doesn't have the packet as sent, return an error.
        if !self.src_chain().chain.get_current_state()?.check_sent(
            &packet.port_id,
            &packet.channel_id,
            &packet.sequence,
        ) {
            return Err(Error::timeout_without_sent(
                self.src_chain().chain.name().to_string(),
                self.dst_chain().chain.name().to_string(),
            ));
        }
        // Must be timed out. Current height > timeout height
        Ok(MockMessage::TimeoutPacket(
            self.src_client_id().clone(),
            destination_height.clone(),
            packet.clone(),
        ))
    }
}
