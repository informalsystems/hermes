use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::ibc_event::IbcEventContext;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::ibc_message_sender::{IbcMessageSenderContext, IbcMessageSenderExt};
use crate::traits::messages::ack_packet::AckPacketMessageBuilder;
use crate::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::traits::target::SourceTarget;
use crate::types::aliases::{Height, Packet, WriteAcknowledgementEvent};

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
        destination_height: &Height<Context::DstChain>,
        packet: &Packet<Context>,
        ack: &WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>,
    ) -> Result<(), Error> {
        let message = context
            .build_ack_packet_message(destination_height, packet, ack)
            .await?;

        context.send_message(message).await?;

        Ok(())
    }
}
