use async_trait::async_trait;

use crate::traits::ibc_event_context::IbcEventContext;
use crate::traits::ibc_message_sender::{
    IbcMessageSenderContext, IbcMessageSenderExt, MismatchIbcEventsCountError,
};
use crate::traits::messages::receive_packet::{ReceivePacketMessageBuilder, ReceivePacketRelayer};
use crate::traits::relay_context::RelayContext;
use crate::traits::target::DestinationTarget;
use crate::types::aliases::{Height, Packet, WriteAcknowledgementEvent};

pub struct BaseReceivePacketRelayer;

#[async_trait]
impl<Context, Error> ReceivePacketRelayer<Context> for BaseReceivePacketRelayer
where
    Context: RelayContext<Error = Error>,
    Context: ReceivePacketMessageBuilder<Context>,
    Context: IbcMessageSenderContext<DestinationTarget>,
    Context::DstChain: IbcEventContext<Context::SrcChain>,
    Context::Error: From<MismatchIbcEventsCountError>,
{
    async fn relay_receive_packet(
        &self,
        context: &Context,
        source_height: &Height<Context::SrcChain>,
        packet: &Packet<Context>,
    ) -> Result<Option<WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>>, Error>
    {
        let message = context
            .build_receive_packet_message(source_height, &packet)
            .await?;

        let events = context
            .ibc_message_sender()
            .send_message_with_events(context, message)
            .await?;

        let ack_event = events.into_iter().find_map(|ev| ev.try_into().ok());

        Ok(ack_event)
    }
}
