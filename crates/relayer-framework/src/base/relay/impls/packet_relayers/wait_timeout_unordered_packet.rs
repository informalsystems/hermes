use core::cmp::Ord;
use core::marker::PhantomData;
use core::time::Duration;

use async_trait::async_trait;

use crate::base::chain::types::aliases::Message;
use crate::base::{
    chain::traits::queries::status::HasChainStatusQuerier,
    core::traits::{runtime::HasRuntime, runtimes::sleep::CanSleep, sync::Async},
    relay::traits::{
        context::HasRelayTypes, messages::timeout_packet::TimeoutUnorderedPacketMessageBuilder,
    },
};
use crate::std_prelude::*;

/// An unordered packet message builder variant that waits for the counterparty
/// chain's height to exceed the source chain's height so that the timeout
/// packet proof can be constructed before broadcasting the timeout packet.
pub struct WaitTimeoutUnorderedPacketMessageBuilder<InMessageBuilder>(
    PhantomData<InMessageBuilder>,
);

#[async_trait]
impl<Relay, InMessageBuilder, Runtime, Height, Error> TimeoutUnorderedPacketMessageBuilder<Relay>
    for WaitTimeoutUnorderedPacketMessageBuilder<InMessageBuilder>
where
    Relay: HasRelayTypes<Error = Error>,
    Relay: HasRuntime<Runtime = Runtime>,
    Relay::DstChain: HasChainStatusQuerier<Height = Height>,
    InMessageBuilder: TimeoutUnorderedPacketMessageBuilder<Relay>,
    Runtime: CanSleep,
    Height: Ord + Async,
{
    async fn build_timeout_unordered_packet_message(
        context: &Relay,
        destination_height: &Height,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error> {
        let chain = context.destination_chain();

        loop {
            let counterparty_status = chain.query_chain_status().await?;
            let counterparty_height = Relay::DstChain::chain_status_height(&counterparty_status);

            if counterparty_height > destination_height {
                return InMessageBuilder::build_timeout_unordered_packet_message(
                    context,
                    destination_height,
                    packet,
                )
                .await;
            } else {
                context.runtime().sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
