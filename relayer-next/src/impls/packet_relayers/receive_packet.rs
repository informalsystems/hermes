use async_trait::async_trait;

use crate::traits::ibc_message_sender::{IbcMessageSenderContext, IbcMessageSenderExt};
use crate::traits::messages::receive_packet::ReceivePacketMessageBuilder;
use crate::traits::packet_relayer::PacketRelayer;
use crate::traits::queries::status::{ChainStatus, ChainStatusQuerier};
use crate::traits::relay_types::RelayContext;
use crate::traits::target::DestinationTarget;
use crate::types::aliases::Packet;

pub struct ReceivePacketRelayer;

#[async_trait]
impl<Context, Error> PacketRelayer<Context> for ReceivePacketRelayer
where
    Context: RelayContext<Error = Error>,
    Context: ReceivePacketMessageBuilder<Context>,
    Context::SrcChain: ChainStatusQuerier<Context::SrcChain>,
    Context: IbcMessageSenderContext<DestinationTarget>,
{
    type Return = ();

    async fn relay_packet(&self, context: &Context, packet: Packet<Context>) -> Result<(), Error> {
        let source_height = context
            .source_context()
            .query_chain_status()
            .await?
            .height();

        let message = context
            .build_receive_packet_message(&source_height, &packet)
            .await?;

        context
            .ibc_message_sender()
            .send_message(context, message)
            .await?;

        Ok(())
    }
}
