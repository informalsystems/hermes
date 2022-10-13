use async_trait::async_trait;

use crate::base::chain::types::aliases::Height;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::context::HasRelayTypes;
use crate::std_prelude::*;

/// Encapsulates the capability of a relayer to send timeout packets over
/// unordered channels.
///
/// Timeout packets are sent from a destination chain to the source chain that
/// originated the timed out message.
///
/// When a timeout packet is sent, a response is not expected to be received.
/// This is in contrast when sending e.g. receive packets, which expect to
/// receive back a `WriteAcknowledgementEvent` in response to the receive
/// packet.
#[async_trait]
pub trait TimeoutUnorderedPacketRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
{
    async fn relay_timeout_unordered_packet(
        context: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait HasTimeoutUnorderedPacketRelayer: HasRelayTypes {
    type TimeoutUnorderedPacketRelayer: TimeoutUnorderedPacketRelayer<Self>;

    async fn relay_timeout_unordered_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
    ) -> Result<(), Self::Error> {
        Self::TimeoutUnorderedPacketRelayer::relay_timeout_unordered_packet(
            self,
            destination_height,
            packet,
        )
        .await
    }
}
