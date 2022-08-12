use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::ibc_event::HasIbcEvents;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;
use crate::types::aliases::{Height, WriteAcknowledgementEvent};

#[async_trait]
pub trait AckPacketRelayer<Context: RelayContext>: Async
where
    Context::DstChain: HasIbcEvents<Context::SrcChain>,
{
    async fn relay_ack_packet(
        &self,
        context: &Context,
        destination_height: &Height<Context::DstChain>,
        packet: &Context::Packet,
        ack: &WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>,
    ) -> Result<(), Context::Error>;
}
