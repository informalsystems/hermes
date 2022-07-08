use async_trait::async_trait;
use ibc::core::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::PacketMsgType;
use ibc::tx_msg::Msg;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::traits::messages::receive_packet::ReceivePacketMessageBuilder;

use crate::cosmos::error::Error;
use crate::cosmos::handler::CosmosRelayHandler;
use crate::cosmos::message::CosmosIbcMessage;

#[async_trait]
impl<SrcChain, DstChain> ReceivePacketMessageBuilder<CosmosRelayHandler<SrcChain, DstChain>>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    async fn build_receive_packet_message(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosIbcMessage, Error> {
        let proofs = self
            .src_handle
            .handle
            .build_packet_proofs(
                PacketMsgType::Recv,
                &packet.source_port,
                &packet.source_channel,
                packet.sequence,
                *height,
            )
            .map_err(Error::relayer)?;

        let packet = packet.clone();

        let message = CosmosIbcMessage::new(Some(*height), move |signer| {
            Ok(MsgRecvPacket::new(packet.clone(), proofs.clone(), signer.clone()).to_any())
        });

        Ok(message)
    }
}
