use async_trait::async_trait;

use crate::base::chain::types::aliases::Height;
use crate::base::relay::traits::ibc_message_sender::{
    CanSendIbcMessages, IbcMessageSenderExt, InjectMismatchIbcEventsCountError,
};
use crate::base::relay::traits::messages::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketMessage;
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer;
use crate::base::relay::traits::target::SourceTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::relay::types::aliases::Packet;
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
    Context: CanBuildTimeoutUnorderedPacketMessage,
    Context: CanSendIbcMessages<SourceTarget>,
    Context: HasRelayTypes,
    Context: InjectMismatchIbcEventsCountError,
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
