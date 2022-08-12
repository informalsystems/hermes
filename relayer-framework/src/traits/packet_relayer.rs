use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;
use crate::types::aliases::Packet;

#[async_trait]
pub trait PacketRelayer<Context>: Async
where
    Context: RelayContext,
{
    async fn relay_packet(
        &self,
        context: &Context,
        packet: &Packet<Context>,
    ) -> Result<(), Context::Error>;
}
