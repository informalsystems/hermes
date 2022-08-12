use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::ibc_event::HasIbcEvents;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;
use crate::types::aliases::{Height, WriteAcknowledgementEvent};

#[async_trait]
pub trait ReceivePacketRelayer<Relay>: Async
where
    Relay: RelayContext,
    Relay::DstChain: HasIbcEvents<Relay::SrcChain>,
{
    async fn relay_receive_packet(
        &self,
        context: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>;
}
