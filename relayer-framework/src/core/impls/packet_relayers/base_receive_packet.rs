use async_trait::async_trait;

use crate::core::traits::contexts::ibc_event::HasIbcEvents;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::traits::ibc_message_sender::{
    HasIbcMessageSender, IbcMessageSenderExt, MismatchIbcEventsCountError,
};
use crate::core::traits::messages::receive_packet::HasReceivePacketMessageBuilder;
use crate::core::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::core::traits::target::DestinationTarget;
use crate::core::types::aliases::{Height, Packet, WriteAcknowledgementEvent};
use crate::std_prelude::*;

pub struct BaseReceivePacketRelayer;

#[async_trait]
impl<Context, Message, Event, AckEvent, DstChain> ReceivePacketRelayer<Context>
    for BaseReceivePacketRelayer
where
    Context: HasReceivePacketMessageBuilder,
    Context: HasIbcMessageSender<DestinationTarget>,
    Context: RelayContext<DstChain = DstChain>,
    DstChain: HasIbcEvents<
        Context::SrcChain,
        WriteAcknowledgementEvent = AckEvent,
        Message = Message,
        Event = Event,
    >,
    Context::Error: From<MismatchIbcEventsCountError>,
    Message: Async,
{
    async fn relay_receive_packet(
        &self,
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
