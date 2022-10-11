use async_trait::async_trait;
use core::cmp::Ord;
use core::marker::PhantomData;

use crate::base::traits::{
    contexts::relay::RelayContext, core::Async,
    messages::timeout_packet::TimeoutUnorderedPacketMessageBuilder, runtime::sleep::CanSleep,
};
use crate::base::types::aliases::Message;
use crate::std_prelude::*;

/// Wait for the chain to reach a height that is greater than the required
/// height so that the timeout packet proof can be built.
pub struct WaitTimeoutUnorderedPacketMessageBuilder<InMessageBuilder>(
    PhantomData<InMessageBuilder>,
);

#[async_trait]
impl<Relay, InMessageBuilder, Height, Error, Runtime> TimeoutUnorderedPacketMessageBuilder<Relay>
    for WaitTimeoutUnorderedPacketMessageBuilder<InMessageBuilder>
where
    Relay: RelayContext<Error = Error, Runtime = Runtime>,
    InMessageBuilder: TimeoutUnorderedPacketMessageBuilder<Relay>,
    Runtime: CanSleep,
    Height: Ord + Async,
{
    async fn build_timeout_unordered_packet_message(
        relay: &Relay,
        destination_height: &Height,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error> {
    }
}
