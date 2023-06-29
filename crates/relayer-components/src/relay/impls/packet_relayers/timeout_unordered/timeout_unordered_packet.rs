use async_trait::async_trait;

use crate::chain::traits::message_builders::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketMessage;
use crate::chain::types::aliases::Height;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::ibc_message_sender::CanSendSingleIbcMessage;
use crate::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer;
use crate::relay::traits::target::SourceTarget;
use crate::relay::types::aliases::Packet;
use crate::std_prelude::*;

/// The minimal component that implements timeout packet relayer
/// capabilities. Timeout packet relayers with more capabilities can be
/// implemented on top of this base type.
pub struct BaseTimeoutUnorderedPacketRelayer;

#[async_trait]
impl<Relay> TimeoutUnorderedPacketRelayer<Relay> for BaseTimeoutUnorderedPacketRelayer
where
    Relay: HasRelayChains,
    Relay: CanSendSingleIbcMessage<SourceTarget>,
    Relay::DstChain: CanBuildTimeoutUnorderedPacketMessage<Relay::SrcChain>,
{
    async fn relay_timeout_unordered_packet(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Packet<Relay>,
    ) -> Result<(), Relay::Error> {
        let message = relay
            .dst_chain()
            .build_timeout_unordered_packet_message(destination_height, packet)
            .await
            .map_err(Relay::dst_chain_error)?;

        relay.send_message(SourceTarget, message).await?;

        Ok(())
    }
}
