use core::marker::PhantomData;

use async_trait::async_trait;

use crate::base::traits::contexts::ibc_event::HasIbcEvents;
use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::packet_relayer::PacketRelayer;
use crate::base::traits::packet_relayers::ack_packet::AckPacketRelayer;
use crate::base::traits::packet_relayers::receive_packet::ReceivePacketRelayer;
use crate::base::traits::queries::status::{HasChainStatus, HasChainStatusQuerier};
use crate::base::types::aliases::Packet;
use crate::std_prelude::*;

pub struct FullRelayer<ReceiveRelay, AckRelay> {
    pub phantom: PhantomData<(ReceiveRelay, AckRelay)>,
}

#[async_trait]
impl<Context, ReceiveRelay, AckRelay> PacketRelayer<Context> for FullRelayer<ReceiveRelay, AckRelay>
where
    Context: RelayContext,
    ReceiveRelay: ReceivePacketRelayer<Context>,
    AckRelay: AckPacketRelayer<Context>,
    Context::DstChain: HasIbcEvents<Context::SrcChain>,
    Context::SrcChain: HasChainStatusQuerier,
    Context::DstChain: HasChainStatusQuerier,
{
    async fn relay_packet(
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error> {
        let source_status = context.source_chain().query_chain_status().await?;

        let write_ack = ReceiveRelay::relay_receive_packet(
            context,
            Context::SrcChain::chain_status_height(&source_status),
            packet,
        )
        .await?;

        if let Some(ack) = write_ack {
            let destination_status = context.destination_chain().query_chain_status().await?;

            AckRelay::relay_ack_packet(
                context,
                Context::DstChain::chain_status_height(&destination_status),
                packet,
                &ack,
            )
            .await?;
        }

        Ok(())
    }
}
