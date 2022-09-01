use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::types::aliases::Height;
use crate::std_prelude::*;

/// Encapsulates the capability of a relayer to send timeout
/// packets over unordered channels. 
///
/// Timeout packets are generally sent back to the source chain.
///
/// When a timeout packet is sent, a response is not expected to 
/// be received. This is in contrast when sending e.g. receive
/// packets, which expect to receive back a `WriteAcknowledgementEvent`
/// in response to the receive packet. 
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
