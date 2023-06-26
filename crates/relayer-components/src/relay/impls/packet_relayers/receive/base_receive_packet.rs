use async_trait::async_trait;

use crate::chain::traits::message_builders::receive_packet::CanBuildReceivePacketMessage;
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::types::aliases::Height;
use crate::relay::traits::ibc_message_sender::{CanSendIbcMessages, IbcMessageSenderExt};
use crate::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::relay::traits::target::DestinationTarget;
use crate::relay::traits::types::HasRelayChains;
use crate::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct BaseReceivePacketRelayer;

#[async_trait]
impl<Relay, AckEvent> ReceivePacketRelayer<Relay> for BaseReceivePacketRelayer
where
    Relay::SrcChain: CanBuildReceivePacketMessage<Relay::DstChain>,
    Relay: CanSendIbcMessages<DestinationTarget>,
    Relay: HasRelayChains,
    Relay::DstChain:
        HasWriteAcknowledgementEvent<Relay::SrcChain, WriteAcknowledgementEvent = AckEvent>,
{
    async fn relay_receive_packet(
        relay: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Packet<Relay>,
    ) -> Result<Option<AckEvent>, Relay::Error> {
        let message = relay
            .src_chain()
            .build_receive_packet_message(source_height, packet)
            .await
            .map_err(Relay::src_chain_error)?;

        let events = relay.send_message(message).await?;

        let ack_event = events
            .iter()
            .find_map(Relay::DstChain::try_extract_write_acknowledgement_event);

        Ok(ack_event)
    }
}
