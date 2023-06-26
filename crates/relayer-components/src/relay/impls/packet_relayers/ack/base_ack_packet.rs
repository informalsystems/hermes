use async_trait::async_trait;

use crate::chain::traits::message_builders::ack_packet::CanBuildAckPacketMessage;
use crate::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::relay::traits::ibc_message_sender::{CanSendIbcMessages, IbcMessageSenderExt};
use crate::relay::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::relay::traits::target::SourceTarget;
use crate::relay::traits::types::HasRelayChains;
use crate::relay::types::aliases::Packet;
use crate::std_prelude::*;

/// The minimal component that can send an acknowledgement packet.
/// Ack packet relayers with more capabilities can be implemented
/// on top of this base type.
pub struct BaseAckPacketRelayer;

#[async_trait]
impl<Relay> AckPacketRelayer<Relay> for BaseAckPacketRelayer
where
    Relay: HasRelayChains,
    Relay: CanSendIbcMessages<SourceTarget>,
    Relay::DstChain: CanBuildAckPacketMessage<Relay::SrcChain>,
{
    async fn relay_ack_packet(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Packet<Relay>,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error> {
        let message = relay
            .dst_chain()
            .build_ack_packet_message(destination_height, packet, ack)
            .await
            .map_err(Relay::dst_chain_error)?;

        relay.send_message(message).await?;

        Ok(())
    }
}
