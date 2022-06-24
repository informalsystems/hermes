use async_trait::async_trait;

use crate::traits::message_sender::IbcMessageSender;
use crate::traits::messages::receive_packet::ReceivePacketMessageBuilder;
use crate::traits::packet_relayer::PacketRelayer;
use crate::traits::queries::status::{ChainStatus, ChainStatusQuerier};
use crate::types::aliases::Packet;

pub struct ReceivePacketRelayer;

#[async_trait]
impl<Context> PacketRelayer<Context> for ReceivePacketRelayer
where
    Context: ReceivePacketMessageBuilder,
    Context::SrcChain: ChainStatusQuerier,
    Context::DstChain: IbcMessageSender<Context::SrcChain>,
{
    type Return = ();
    type Error = Context::Error;

    async fn relay_packet(
        &self,
        context: &Context,
        packet: Packet<Context>,
    ) -> Result<Self::Return, Self::Error> {
        let source_height = context.source_chain().query_chain_status().await?.height();

        let message = context
            .build_receive_packet_message(&source_height, &packet)
            .await?;

        context.destination_chain().send_message(message).await?;

        Ok(())
    }
}
