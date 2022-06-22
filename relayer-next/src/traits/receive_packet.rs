use async_trait::async_trait;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::Height;

use super::context::RelayContext;
use crate::tagged::{DualTagged, MonoTagged};
use crate::types::message::Message;

#[async_trait]
pub trait ReceivePacketMessageBuilder: RelayContext {
    async fn build_receive_packet_message(
        &self,
        height: MonoTagged<Self::SrcChain, Height>,
        port_id: DualTagged<Self::SrcChain, Self::DstChain, PortId>,
        channel_id: DualTagged<Self::SrcChain, Self::DstChain, ChannelId>,
        sequence: DualTagged<Self::SrcChain, Self::DstChain, Sequence>,
    ) -> Result<Message<Self::DstChain, Self::SrcChain>, Self::Error>;
}
