use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::types::aliases::Height;
use crate::std_prelude::*;

#[async_trait]
pub trait TimeoutUnorderedPacketRelayer<Relay>: Async
where
    Relay: RelayContext,
{
    async fn relay_timeout_unordered_packet(
        &self,
        context: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<(), Relay::Error>;
}
