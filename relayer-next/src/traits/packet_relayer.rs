use async_trait::async_trait;

use crate::traits::relay_context::RelayContext;
use crate::types::aliases::Packet;

#[async_trait]
pub trait PacketRelayer: RelayContext {
    type Context: RelayContext;
    type Return;

    async fn relay(&self, packet: Packet<Self::Context>) -> Result<Self::Return, Self::Error>;
}
