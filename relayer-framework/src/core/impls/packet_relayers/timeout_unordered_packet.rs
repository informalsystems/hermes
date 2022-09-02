use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::ibc_message_sender::{
    HasIbcMessageSender, IbcMessageSenderExt, MismatchIbcEventsCountError,
};
use crate::core::traits::messages::timeout_packet::HasTimeoutUnorderedPacketMessageBuilder;
use crate::core::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer;
use crate::core::traits::target::SourceTarget;
use crate::core::types::aliases::{Height, Packet};
use crate::std_prelude::*;

pub struct BaseTimeoutUnorderedPacketRelayer;

impl Default for BaseTimeoutUnorderedPacketRelayer {
    fn default() -> Self {
        BaseTimeoutUnorderedPacketRelayer
    }
}

#[async_trait]
impl<Context> TimeoutUnorderedPacketRelayer<Context> for BaseTimeoutUnorderedPacketRelayer
where
    Context: HasTimeoutUnorderedPacketMessageBuilder,
    Context: HasIbcMessageSender<SourceTarget>,
    Context: RelayContext,
    Context::Error: From<MismatchIbcEventsCountError>,
{
    async fn relay_timeout_unordered_packet(
        &self,
        context: &Context,
        destination_height: &Height<Context::DstChain>,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        let message = context
            .build_timeout_unordered_packet_message(destination_height, packet)
            .await?;

        context.send_message(message).await?;

        Ok(())
    }
}
