use async_trait::async_trait;

use crate::traits::relay_types::RelayContext;
use crate::types::aliases::Packet;

#[async_trait]
pub trait PacketRelayer<Context: RelayContext> {
    type Return;

    async fn relay_packet(
        &self,
        context: &Context,
        packet: Packet<Context::RelayTypes>,
    ) -> Result<Self::Return, Context::Error>;
}
