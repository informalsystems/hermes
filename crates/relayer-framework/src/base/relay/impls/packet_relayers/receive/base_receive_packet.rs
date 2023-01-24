use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasWriteAcknowledgementEvent;
use crate::base::chain::traits::message::receive_packet::CanBuildReceivePacketMessage;
use crate::base::chain::types::aliases::Height;
use crate::base::relay::traits::ibc_message_sender::{CanSendIbcMessages, IbcMessageSenderExt};
use crate::base::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::base::relay::traits::target::DestinationTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::relay::types::aliases::Packet;
use crate::std_prelude::*;

pub struct BaseReceivePacketRelayer;

#[async_trait]
impl<Relay, AckEvent> ReceivePacketRelayer<Relay> for BaseReceivePacketRelayer
where
    Relay::SrcChain: CanBuildReceivePacketMessage<Relay::DstChain>,
    Relay: CanSendIbcMessages<DestinationTarget>,
    Relay: HasRelayTypes,
    Relay::DstChain:
        HasWriteAcknowledgementEvent<Relay::SrcChain, WriteAcknowledgementEvent = AckEvent>,
{
    async fn relay_receive_packet(
        relay: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Packet<Relay>,
    ) -> Result<Option<AckEvent>, Relay::Error> {
        let message = relay
            .source_chain()
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
