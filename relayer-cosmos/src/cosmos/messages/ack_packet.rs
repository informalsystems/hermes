use async_trait::async_trait;
use ibc::core::ics04_channel::msgs::acknowledgement::MsgAcknowledgement;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::PacketMsgType;
use ibc::tx_msg::Msg;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::traits::messages::ack_packet::AckPacketMessageBuilder;

use crate::cosmos::context::chain::WriteAcknowledgementEvent;
use crate::cosmos::context::relay::CosmosRelayContext;
use crate::cosmos::error::Error;
use crate::cosmos::message::CosmosIbcMessage;

#[async_trait]
impl<SrcChain, DstChain> AckPacketMessageBuilder<CosmosRelayContext<SrcChain, DstChain>>
    for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    async fn build_ack_packet_message(
        &self,
        destination_height: &Height,
        packet: &Packet,
        event: &WriteAcknowledgementEvent,
    ) -> Result<CosmosIbcMessage, Error> {
        let proofs = self
            .dst_handle
            .handle
            .build_packet_proofs(
                PacketMsgType::Ack,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                *destination_height,
            )
            .map_err(Error::relayer)?;

        let packet = packet.clone();
        let ack = event.0.ack.clone();

        let message = CosmosIbcMessage::new(Some(destination_height.clone()), move |signer| {
            Ok(MsgAcknowledgement::new(
                packet.clone(),
                ack.clone().into(),
                proofs.clone(),
                signer.clone(),
            )
            .to_any())
        });

        Ok(message)
    }
}
