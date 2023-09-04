use async_trait::async_trait;

use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::message_builders::receive_packet::{
    CanBuildReceivePacketMessage, CanBuildReceivePacketPayload,
};
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::types::aliases::Height;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::ibc_message_sender::{CanSendSingleIbcMessage, MainSink};
use crate::relay::traits::components::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::relay::traits::target::DestinationTarget;
use crate::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct BaseReceivePacketRelayer;

#[async_trait]
impl<Relay, AckEvent> ReceivePacketRelayer<Relay> for BaseReceivePacketRelayer
where
    Relay: HasRelayChains + CanSendSingleIbcMessage<MainSink, DestinationTarget>,
    Relay::SrcChain: CanBuildReceivePacketPayload<Relay::DstChain>,
    Relay::DstChain: CanQueryClientState<Relay::SrcChain>
        + CanBuildReceivePacketMessage<Relay::SrcChain>
        + HasWriteAcknowledgementEvent<Relay::SrcChain, WriteAcknowledgementEvent = AckEvent>,
{
    async fn relay_receive_packet(
        relay: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Packet<Relay>,
    ) -> Result<Option<AckEvent>, Relay::Error> {
        let src_client_state = relay
            .dst_chain()
            .query_client_state(relay.dst_client_id())
            .await
            .map_err(Relay::dst_chain_error)?;

        let payload = relay
            .src_chain()
            .build_receive_packet_payload(&src_client_state, source_height, packet)
            .await
            .map_err(Relay::src_chain_error)?;

        let message = relay
            .dst_chain()
            .build_receive_packet_message(packet, payload)
            .await
            .map_err(Relay::dst_chain_error)?;

        let events = relay.send_message(DestinationTarget, message).await?;

        let ack_event = events
            .iter()
            .find_map(Relay::DstChain::try_extract_write_acknowledgement_event);

        Ok(ack_event)
    }
}
