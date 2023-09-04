use async_trait::async_trait;

use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::message_builders::ack_packet::{
    CanBuildAckPacketMessage, CanBuildAckPacketPayload,
};
use crate::chain::traits::types::client_state::HasClientStateType;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::core::traits::sync::Async;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::ibc_message_sender::{CanSendSingleIbcMessage, MainSink};
use crate::relay::traits::components::packet_relayers::ack_packet::AckPacketRelayer;
use crate::relay::traits::target::SourceTarget;
use crate::std_prelude::*;

/// The minimal component that can send an acknowledgement packet.
/// Ack packet relayers with more capabilities can be implemented
/// on top of this base type.
pub struct BaseAckPacketRelayer;

#[async_trait]
impl<Relay, SrcChain, DstChain, Packet> AckPacketRelayer<Relay> for BaseAckPacketRelayer
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain, Packet = Packet>,
    Relay: CanSendSingleIbcMessage<MainSink, SourceTarget>,
    SrcChain: CanQueryClientState<DstChain>
        + CanBuildAckPacketMessage<DstChain>
        + HasIbcPacketTypes<DstChain, OutgoingPacket = Packet>,
    DstChain: HasClientStateType<SrcChain>
        + CanBuildAckPacketPayload<SrcChain>
        + HasIbcPacketTypes<SrcChain, IncomingPacket = Packet>,
    Packet: Async,
{
    async fn relay_ack_packet(
        relay: &Relay,
        destination_height: &DstChain::Height,
        packet: &Packet,
        ack: &DstChain::WriteAcknowledgementEvent,
    ) -> Result<(), Relay::Error> {
        let src_client_state = relay
            .src_chain()
            .query_client_state(relay.src_client_id())
            .await
            .map_err(Relay::src_chain_error)?;

        let payload = relay
            .dst_chain()
            .build_ack_packet_payload(&src_client_state, destination_height, packet, ack)
            .await
            .map_err(Relay::dst_chain_error)?;

        let message = relay
            .src_chain()
            .build_ack_packet_message(packet, payload)
            .await
            .map_err(Relay::src_chain_error)?;

        relay.send_message(SourceTarget, message).await?;

        Ok(())
    }
}
