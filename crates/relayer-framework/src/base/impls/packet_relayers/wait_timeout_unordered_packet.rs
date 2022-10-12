use async_trait::async_trait;
use core::cmp::Ord;
use core::marker::PhantomData;
use core::time::Duration;

use crate::base::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::base::traits::queries::status::HasChainStatusQuerier;
use crate::base::traits::target::ChainTarget;
use crate::base::traits::{
    contexts::relay::RelayContext, core::Async,
    messages::timeout_packet::TimeoutUnorderedPacketMessageBuilder, runtime::sleep::CanSleep,
};
use crate::base::types::aliases::Message;
use crate::std_prelude::*;

/// An unordered packet message builder variant that waits for the counterparty
/// chain's height to exceed the source chain's height so that the timeout
/// packet proof can be constructed before broadcasting the timeout packet.
pub struct WaitTimeoutUnorderedPacketMessageBuilder<InMessageBuilder, Target>(
    PhantomData<InMessageBuilder>,
    PhantomData<Target>,
);

#[async_trait]
impl<Relay, Target, TargetChain, InMessageBuilder, CounterpartyChain, Height, Error, Runtime>
    TimeoutUnorderedPacketMessageBuilder<Relay>
    for WaitTimeoutUnorderedPacketMessageBuilder<InMessageBuilder, Target>
where
    Relay: RelayContext<Error = Error, Runtime = Runtime>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    TargetChain: IbcChainContext<CounterpartyChain>,
    CounterpartyChain: IbcChainContext<TargetChain, Height = Height, Error = Error>,
    CounterpartyChain: HasChainStatusQuerier,
    Relay::DstChain: ChainContext<Height = Height>,
    InMessageBuilder: TimeoutUnorderedPacketMessageBuilder<Relay>,
    Runtime: CanSleep,
    Height: Ord + Async,
{
    async fn build_timeout_unordered_packet_message(
        context: &Relay,
        destination_height: &Height,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::SrcChain>, Relay::Error> {
        let chain = Target::counterparty_chain(context);

        loop {
            let current_status = chain.query_chain_status().await?;
            let current_height = CounterpartyChain::chain_status_height(&current_status);

            if current_height > destination_height {
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
