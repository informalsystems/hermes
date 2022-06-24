use async_trait::async_trait;
use ibc::core::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use ibc::core::ics04_channel::packet::PacketMsgType;
use ibc::tx_msg::Msg;
use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::impls::cosmos::relay_context::CosmosRelayContext;
use crate::traits::messages::receive_packet::ReceivePacketMessageBuilder;
use crate::types::aliases::{Height, IbcMessage, Packet};

#[async_trait]
impl<SrcChain, DstChain> ReceivePacketMessageBuilder for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    async fn build_receive_packet_message(
        &self,
        height: &Height<Self::SrcChain>,
        packet: &Packet<Self>,
    ) -> Result<IbcMessage<Self::DstChain, Self::SrcChain>, Self::Error> {
        let proofs = self
            .source_chain
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
            Ok(MsgRecvPacket::new(packet, proofs.clone(), signer).to_any())
        });

        Ok(message)
    }
}
