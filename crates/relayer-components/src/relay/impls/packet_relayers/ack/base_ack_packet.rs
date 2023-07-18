use async_trait::async_trait;

use crate::chain::traits::message_builders::ack_packet::{
    CanBuildAckPacketMessage, CanBuildAckPacketPayload,
};
use crate::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::ibc_message_sender::CanSendSingleIbcMessage;
use crate::relay::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::relay::traits::target::SourceTarget;
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
    Relay: CanSendSingleIbcMessage<SourceTarget>,
    Relay::DstChain: CanBuildAckPacketPayload<Relay::SrcChain>,
    Relay::SrcChain: CanBuildAckPacketMessage<Relay::DstChain>,
{
    async fn relay_ack_packet(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Packet<Relay>,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error> {
        let payload = relay
            .dst_chain()
            .build_ack_packet_payload(destination_height, packet, ack)
            .await
            .map_err(Relay::dst_chain_error)?;

        let message = relay
            .src_chain()
            .build_ack_packet_message(payload)
            .await
            .map_err(Relay::src_chain_error)?;

        relay.send_message(SourceTarget, message).await?;

        Ok(())
    }
}
