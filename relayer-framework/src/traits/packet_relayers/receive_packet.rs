use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::ibc_event::IbcEventContext;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;
use crate::types::aliases::{Height, WriteAcknowledgementEvent};

#[async_trait]
pub trait ReceivePacketRelayer<Context: RelayContext>: Async
where
    Context::DstChain: IbcEventContext<Context::SrcChain>,
{
    async fn relay_receive_packet(
        &self,
        context: &Context,
        source_height: &Height<Context::SrcChain>,
        packet: &Context::Packet,
    ) -> Result<
        Option<WriteAcknowledgementEvent<Context::DstChain, Context::SrcChain>>,
        Context::Error,
    >;
}
