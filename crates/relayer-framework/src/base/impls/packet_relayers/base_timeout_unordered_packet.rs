use async_trait::async_trait;

use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::ibc_message_sender::{
    HasIbcMessageSender, IbcMessageSenderExt, MismatchIbcEventsCountError,
};
use crate::base::traits::messages::timeout_packet::HasTimeoutUnorderedPacketMessageBuilder;
use crate::base::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer;
use crate::base::traits::target::SourceTarget;
use crate::base::types::aliases::{Height, Packet};
use crate::std_prelude::*;

/// The lowest-level minimal type that implements timeout packet relayer
/// capabilities. Timeout packet relayers with more capabilities can be
/// implemented on top of this base type.
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
