use async_trait::async_trait;

use crate::core::traits::contexts::ibc_event::HasIbcEvents;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::traits::ibc_message_sender::{
    HasIbcMessageSender, IbcMessageSenderExt, MismatchIbcEventsCountError,
};
use crate::core::traits::messages::timeout_packet::HasTimeoutUnorderedPacketMessageBuilder;
use crate::core::traits::packet_relayers::timeout_packet::TimeoutUnorderedPacketRelayer;
use crate::std_prelude::*;

pub struct BaseTimeoutUnorderedPacketRelayer;

#[async_trait]
impl<Context, Message, Event, AckEvent, DstChain> TimeoutUnorderedPacketRelayer<Context>
    for BaseTimeoutUnorderedPacketRelayer
where
    Context: HasTimeoutUnorderedPacketMessageBuilder,
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
    async fn relay_timeout_unordered_packet(
        &self,
        context: &Context,
        destination_height: &Height<Context::DstChain>,
        packet: &Packet<Context>,
    ) -> Result<Option<WriteAcknowledgementEvent<DstChain, Context::SrcChain>>, Context::Error>
    {

    }
}
