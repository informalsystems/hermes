use async_trait::async_trait;

use ibc_relayer_framework::base::one_for_all::traits::chain::OfaChainTypes;
use ibc_relayer_framework::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayTypes};
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::common::one_for_all::presets::MinimalPreset;
use ibc_relayer_framework::common::one_for_all::types::chain::OfaChainWrapper;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::relayer_mock::base::types::packet::PacketKey;
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;
use crate::relayer_mock::contexts::relay::MockRelayContext;

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
    fn is_retryable_error(_e: &Self::Error) -> bool {
        unimplemented!()
    }

    fn max_retry_exceeded_error(_e: Self::Error) -> Self::Error {
        unimplemented!()
    }

    fn mismatch_ibc_events_count_error(_expected: usize, _actual: usize) -> Self::Error {
        unimplemented!()
    }

    fn packet_src_channel_id(_packet: &PacketKey) -> &String {
        unimplemented!()
    }

    fn packet_src_port(_packet: &PacketKey) -> &String {
        unimplemented!()
    }

    fn packet_dst_port(packet: &PacketKey) -> &String {
        &packet.port_id
    }

    fn packet_dst_channel_id(packet: &PacketKey) -> &String {
        &packet.channel_id
    }

    fn packet_sequence(packet: &PacketKey) -> &u128 {
        &packet.sequence
    }

    fn packet_timeout_height(_packet: &PacketKey) -> Option<&u128> {
        unimplemented!()
    }

    fn packet_timeout_timestamp(_packet: &Self::Packet) -> &MockHeight {
        unimplemented!()
    }

    fn runtime(&self) -> &OfaRuntimeContext<MockRuntimeContext> {
        &self.runtime
    }

    fn src_client_id(&self) -> &<Self::SrcChain as OfaChainTypes>::ClientId {
        self.src_to_dst_client()
    }

    fn src_chain(&self) -> &OfaChainWrapper<MockChainContext> {
        &self.src_chain
    }

    fn dst_client_id(&self) -> &<Self::DstChain as OfaChainTypes>::ClientId {
        self.dst_to_src_client()
    }

    fn dst_chain(
        &self,
    ) -> &ibc_relayer_framework::common::one_for_all::types::chain::OfaChainWrapper<Self::DstChain>
    {
        &self.dst_chain
    }

    async fn build_src_update_client_messages(
        &self,
        height: &<Self::DstChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::SrcChain as OfaChainTypes>::Message>, Self::Error> {
        Ok(vec![format!("src_update:{}", height)])
    }

    async fn build_dst_update_client_messages(
        &self,
        height: &<Self::SrcChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Self::DstChain as OfaChainTypes>::Message>, Self::Error> {
        Ok(vec![format!("dst_update:{}", height)])
    }

    async fn build_receive_packet_message(
        &self,
        height: &<Self::SrcChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
    ) -> Result<<Self::DstChain as OfaChainTypes>::Message, Self::Error> {
        Ok(format!(
            "{}/{}:recv-{}:{}-{}",
            packet.channel_id, packet.port_id, packet.sequence, height, packet.height
        ))
    }

    async fn build_ack_packet_message(
        &self,
        destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
        _ack: &<Self::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error> {
        Ok(format!(
            "{}/{}:ack-{}:{}-{}",
            packet.channel_id, packet.port_id, packet.sequence, destination_height, packet.height
        ))
    }

    async fn build_timeout_unordered_packet_message(
        &self,
        _destination_height: &<Self::DstChain as OfaChainTypes>::Height,
        _packet: &Self::Packet,
    ) -> Result<<Self::SrcChain as OfaChainTypes>::Message, Self::Error> {
        unimplemented!()
    }
}
