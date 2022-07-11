use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::core::Async;
use crate::traits::ibc_event_context::IbcEventContext;
use crate::traits::relay_context::RelayContext;
use crate::types::aliases::{Height, WriteAcknowledgementEvent};

#[async_trait]
pub trait AckPacketRelayer<Context: RelayContext>: Async
where
    Context::DstChain: IbcEventContext<Context::SrcChain>,
{
    async fn relay_ack_packet(
        &self,
        context: &Context,
        destination_height: &Height<Context::DstChain>,
        packet: &Context::Packet,
        ack: &WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>,
    ) -> Result<(), Context::Error>;
}
