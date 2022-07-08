use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::core::Async;
use crate::traits::ibc_event_context::IbcEventContext;
use crate::traits::relay_context::RelayContext;
use crate::types::aliases::{Height, IbcMessage, WriteAcknowledgementEvent};

#[async_trait]
pub trait ReceivePacketMessageBuilder<Relay: RelayContext> {
    async fn build_receive_packet_message(
        &self,
        height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<IbcMessage<Relay::DstChain, Relay::SrcChain>, Relay::Error>;
}

#[async_trait]
pub trait ReceivePacketRelayer<Context: RelayContext>: Async
where
    Context::DstChain: IbcEventContext<Context::SrcChain>,
{
    async fn relay_receive_packet(
        &self,
        context: &Context,
        source_height: &Height<Context::SrcChain>,
        packet: &Context::Packet,
    ) -> Result<
        Option<WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>>,
        Context::Error,
    >;
}
