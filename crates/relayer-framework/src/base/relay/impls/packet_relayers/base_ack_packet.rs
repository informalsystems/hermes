use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::base::relay::traits::context::HasRelayTypes;
use crate::base::relay::traits::ibc_message_sender::{HasIbcMessageSender, IbcMessageSenderExt};
use crate::base::relay::traits::messages::ack_packet::HasAckPacketMessageBuilder;
use crate::base::relay::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::base::relay::traits::target::SourceTarget;
use crate::base::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct BaseAckPacketRelayer;

#[async_trait]
impl<Context, Error> AckPacketRelayer<Context> for BaseAckPacketRelayer
where
    Context::DstChain: HasIbcEvents<Context::SrcChain>,
    Context: HasRelayTypes<Error = Error>,
    Context: HasAckPacketMessageBuilder,
    Context: HasIbcMessageSender<SourceTarget>,
{
    async fn relay_ack_packet(
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
