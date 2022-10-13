use core::cmp::Ord;
use core::marker::PhantomData;
use core::time::Duration;

use async_trait::async_trait;

use crate::base::chain::traits::context::HasChainTypes;
use crate::base::chain::types::aliases::Message;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::{
    chain::traits::{context::HasIbcChainTypes, queries::status::HasChainStatusQuerier},
    core::traits::{runtime::HasRuntime, runtimes::sleep::CanSleep, sync::Async},
    relay::traits::{
        context::HasRelayTypes, messages::timeout_packet::TimeoutUnorderedPacketMessageBuilder,
    },
};
use crate::std_prelude::*;

/// An unordered packet message builder variant that waits for the counterparty
/// chain's height to exceed the source chain's height so that the timeout
/// packet proof can be constructed before broadcasting the timeout packet.
pub struct WaitTimeoutUnorderedPacketMessageBuilder<InMessageBuilder, Target>(
    PhantomData<InMessageBuilder>,
    PhantomData<Target>,
);

#[async_trait]
impl<Relay, Target, TargetChain, InMessageBuilder, CounterpartyChain, Runtime, Height, Error>
    TimeoutUnorderedPacketMessageBuilder<Relay>
    for WaitTimeoutUnorderedPacketMessageBuilder<InMessageBuilder, Target>
where
    Relay: HasRelayTypes<Error = Error>,
    Relay: HasRuntime<Runtime = Runtime>,
    Relay::DstChain: HasChainTypes<Height = Height>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    TargetChain: HasIbcChainTypes<CounterpartyChain>,
    InMessageBuilder: TimeoutUnorderedPacketMessageBuilder<Relay>,
    CounterpartyChain: HasIbcChainTypes<TargetChain, Height = Height, Error = Error>,
    CounterpartyChain: HasChainStatusQuerier,
    Runtime: CanSleep,
    Height: Ord + Async,
{
    async fn build_timeout_unordered_packet_message(
        context: &Relay,
        height: &Height,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error> {
        let chain = Target::counterparty_chain(context);

        loop {
            let current_status = chain.query_chain_status().await?;
            let current_height = CounterpartyChain::chain_status_height(&current_status);

            if current_height > height {
                return InMessageBuilder::build_timeout_unordered_packet_message(
                    context, height, packet,
                )
                .await;
            } else {
                context.runtime().sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
