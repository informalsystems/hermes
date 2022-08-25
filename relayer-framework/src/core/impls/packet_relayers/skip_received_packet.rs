use async_trait::async_trait;

use crate::core::traits::contexts::ibc_event::HasIbcEvents;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::packet::IbcPacket;
use crate::core::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::core::traits::queries::received_packet::HasReceivedPacketQuerier;
use crate::core::types::aliases::{Height, Packet, WriteAcknowledgementEvent};
use crate::std_prelude::*;

pub struct SkipReceivedPacketRelayer<Relayer> {
    pub relayer: Relayer,
}

impl<Relayer> SkipReceivedPacketRelayer<Relayer> {
    pub fn new(relayer: Relayer) -> Self {
        Self { relayer }
    }
}

#[async_trait]
impl<Context, Relayer> ReceivePacketRelayer<Context> for SkipReceivedPacketRelayer<Relayer>
where
    Context: RelayContext,
    Relayer: ReceivePacketRelayer<Context>,
    Context::DstChain: HasIbcEvents<Context::SrcChain>,
    Context::DstChain: HasReceivedPacketQuerier<Context::SrcChain>,
{
    async fn relay_receive_packet(
        &self,
        context: &Context,
        source_height: &Height<Context::SrcChain>,
        packet: &Packet<Context>,
    ) -> Result<
        Option<WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>>,
        Context::Error,
    > {
        let is_packet_received = context
            .destination_chain()
            .is_packet_received(
                packet.destination_port(),
                packet.destination_channel_id(),
                packet.sequence(),
            )
            .await?;

        if !is_packet_received {
            self.relayer
                .relay_receive_packet(context, source_height, packet)
                .await
        } else {
            Ok(None)
        }
    }
}
