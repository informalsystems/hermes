use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::ibc_event::HasIbcEvents;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::packet::IbcPacket;
use crate::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::traits::queries::received_packet::CanQueryReceivedPacket;
use crate::types::aliases::{Height, Packet, WriteAcknowledgementEvent};

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
    Context::DstChain: CanQueryReceivedPacket<Context::SrcChain>,
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
