use async_trait::async_trait;

use crate::traits::ibc_event_context::IbcEventContext;
use crate::traits::relay_context::RelayContext;
use crate::types::aliases::{IbcMessage, WriteAcknowledgementEvent};

#[async_trait]
pub trait AckPacketMessageBuilder<Context: RelayContext>
where
    Context::DstChain: IbcEventContext<Context::SrcChain>,
{
    async fn build_ack_packet_message(
        &self,
        packet: &Context::Packet,
        ack: &WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>,
    ) -> Result<IbcMessage<Context::SrcChain, Context::DstChain>, Context::Error>;
}

#[async_trait]
pub trait AckPacketRelayer<Context: RelayContext>
where
    Context::DstChain: IbcEventContext<Context::SrcChain>,
{
    async fn relay_ack_packet(
        &self,
        context: &Context,
        packet: Context::Packet,
        ack: &WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>,
    ) -> Result<(), Context::Error>;
}
