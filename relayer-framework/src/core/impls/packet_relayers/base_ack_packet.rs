use async_trait::async_trait;

use crate::core::traits::contexts::ibc_event::HasIbcEvents;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::ibc_message_sender::{HasIbcMessageSender, IbcMessageSenderExt};
use crate::core::traits::messages::ack_packet::HasAckPacketMessageBuilder;
use crate::core::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::core::traits::target::SourceTarget;
use crate::core::types::aliases::{Height, Packet, WriteAcknowledgementEvent};
use crate::std_prelude::*;

pub struct BaseAckPacketRelayer;

#[async_trait]
impl<Context, Error> AckPacketRelayer<Context> for BaseAckPacketRelayer
where
    Context::DstChain: HasIbcEvents<Context::SrcChain>,
    Context: RelayContext<Error = Error>,
    Context: HasAckPacketMessageBuilder,
    Context: HasIbcMessageSender<SourceTarget>,
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
