use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::ibc_message_sender::{CanSendIbcMessages, IbcMessageSenderExt};
use crate::base::relay::traits::messages::receive_packet::CanBuildReceivePacketMessage;
use crate::base::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::base::relay::traits::target::DestinationTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct BaseReceivePacketRelayer;

#[async_trait]
impl<Context, Message, Event, AckEvent, DstChain> ReceivePacketRelayer<Context>
    for BaseReceivePacketRelayer
where
    Context: CanBuildReceivePacketMessage,
    Context: CanSendIbcMessages<DestinationTarget>,
    Context: HasRelayTypes<DstChain = DstChain>,
    DstChain: HasIbcEvents<
        Context::SrcChain,
        WriteAcknowledgementEvent = AckEvent,
        Message = Message,
        Event = Event,
    >,
    Message: Async,
{
    async fn relay_receive_packet(
        context: &Context,
        source_height: &Height<Context::SrcChain>,
        packet: &Packet<Context>,
    ) -> Result<Option<WriteAcknowledgementEvent<DstChain, Context::SrcChain>>, Context::Error>
    {
        let message = context
            .build_receive_packet_message(source_height, packet)
            .await?;

        let events = context.send_message(message).await?;

        let ack_event = events
            .into_iter()
            .find_map(DstChain::try_extract_write_acknowledgement_event);

        Ok(ack_event)
    }
}
