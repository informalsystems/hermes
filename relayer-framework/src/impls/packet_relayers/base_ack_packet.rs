use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::ibc_event_context::IbcEventContext;
use crate::traits::ibc_message_sender::{IbcMessageSenderContext, IbcMessageSenderExt};
use crate::traits::messages::ack_packet::{AckPacketMessageBuilder, AckPacketRelayer};
use crate::traits::relay_context::RelayContext;
use crate::traits::target::SourceTarget;
use crate::types::aliases::{Packet, WriteAcknowledgementEvent};

pub struct BaseAckPacketRelayer;

#[async_trait]
impl<Context, Error> AckPacketRelayer<Context> for BaseAckPacketRelayer
where
    Context::DstChain: IbcEventContext<Context::SrcChain>,
    Context: RelayContext<Error = Error>,
    Context: AckPacketMessageBuilder<Context>,
    Context: IbcMessageSenderContext<SourceTarget>,
{
    async fn relay_ack_packet(
        &self,
        context: &Context,
        packet: Packet<Context>,
        ack: &WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>,
    ) -> Result<(), Error> {
        let message = context.build_ack_packet_message(&packet, ack).await?;

        context.send_message(message).await?;

        Ok(())
    }
}
