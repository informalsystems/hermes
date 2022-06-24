use async_trait::async_trait;

use crate::traits::relay_context::RelayContext;
use crate::types::aliases::Packet;

#[async_trait]
pub trait PacketRelayer<Context: RelayContext> {
    type Return;
    type Error;

    async fn relay_packet(
        &self,
        context: &Context,
        packet: Packet<Context>,
    ) -> Result<Self::Return, Self::Error>;
}
