use async_trait::async_trait;

use crate::base::chain::traits::message::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketMessage;
use crate::base::chain::types::aliases::Height;
use crate::base::relay::traits::ibc_message_sender::{CanSendIbcMessages, IbcMessageSenderExt};
use crate::base::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer;
use crate::base::relay::traits::target::SourceTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::relay::types::aliases::Packet;
use crate::std_prelude::*;

/// The minimal component that implements timeout packet relayer
/// capabilities. Timeout packet relayers with more capabilities can be
/// implemented on top of this base type.
pub struct BaseTimeoutUnorderedPacketRelayer;

#[async_trait]
impl<Relay> TimeoutUnorderedPacketRelayer<Relay> for BaseTimeoutUnorderedPacketRelayer
where
    Relay: HasRelayTypes,
    Relay: CanSendIbcMessages<SourceTarget>,
    Relay::DstChain: CanBuildTimeoutUnorderedPacketMessage<Relay::SrcChain>,
{
    async fn relay_timeout_unordered_packet(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Packet<Relay>,
    ) -> Result<(), Relay::Error> {
        let message = relay
            .destination_chain()
            .build_timeout_unordered_packet_message(destination_height, packet)
            .await
            .map_err(Relay::dst_chain_error)?;

        relay.send_message(message).await?;

        Ok(())
    }
}
