use async_trait::async_trait;

use crate::chain::types::aliases::{Height, Message};
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

/// Encapsulates the capability of the implementer to construct a timeout
/// message that gets sent over an unordered channel from a destination chain
/// to the source chain that originated the message that has timed out.
#[async_trait]
pub trait TimeoutUnorderedPacketMessageBuilder<Relay>
where
    Relay: HasRelayPacket,
{
    async fn build_timeout_unordered_packet_message(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error>;
}

/// A type that implements this trait has the capability to construct a
/// timeout message that gets sent over an unordered channel from a
/// destination chain to the source chain that originated the timed out message.
#[async_trait]
pub trait CanBuildTimeoutUnorderedPacketMessage: HasRelayPacket {
    async fn build_timeout_unordered_packet_message(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
    ) -> Result<Message<Self::SrcChain>, Self::Error>;
}
