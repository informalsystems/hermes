use async_trait::async_trait;

use crate::core::traits::contexts::ibc_event::HasIbcEvents;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::std_prelude::*;

#[async_trait]
pub trait AckPacketRelayer<Relay>: Async
where
    Relay: RelayContext,
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
{
    async fn relay_ack_packet(
        &self,
        context: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error>;
}
