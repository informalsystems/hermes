use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::types::aliases::Height;
use crate::std_prelude::*;

/// Encapsulates the capability for the relayer to send
/// timeout packets over unordered channels. 
///
/// Timeout packets are generally sent to the source chain.
///
/// Compared to e.g. receive packets, which expect to 
/// receive back a `WriteAcknowledgementEvent` in response
/// to the receive packet, timeout packets do not expect
/// to receive any response from the destination chain.
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
