use core::marker::PhantomData;

use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::wait::CanWaitChainReachHeight;
use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::update_client_message_builder::UpdateClientMessageBuilder;
use crate::relay::traits::logs::logger::CanLogRelayTarget;
use crate::relay::traits::target::ChainTarget;
use crate::runtime::traits::runtime::HasRuntime;
use crate::std_prelude::*;

/**
   Wait for the chain to reach a height that is greater than or equal the required height,
   so that the update client proof can be built.
*/
pub struct WaitUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

#[async_trait]
impl<Relay, Target, InUpdateClient, TargetChain, CounterpartyChain>
    UpdateClientMessageBuilder<Relay, Target> for WaitUpdateClient<InUpdateClient>
where
    Relay: HasRelayChains + HasRuntime + CanLogRelayTarget<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    TargetChain: HasIbcChainTypes<CounterpartyChain>,
    CounterpartyChain: CanWaitChainReachHeight + HasIbcChainTypes<TargetChain>,
{
    async fn build_update_client_messages(
        relay: &Relay,
        target: Target,
        height: &CounterpartyChain::Height,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let counterparty_chain = Target::counterparty_chain(relay);

        relay.log_relay_target(
            Relay::Logger::LEVEL_TRACE,
            "waiting for counterparty chain to reach height",
            |log| {
                log.display("target_height", height);
            },
        );

        // We wait for the chain to reach the target height, which may have not been reached
        // when IBC messages are built. This is because proofs build at a latest height would
        // require the chain to progress at least one more height before the update client
        // message can be built.
        let current_height = counterparty_chain
            .wait_chain_reach_height(height)
            .await
            .map_err(Target::counterparty_chain_error)?;

        relay.log_relay_target(
            Relay::Logger::LEVEL_TRACE,
            "counterparty chain's height is now greater than or equal to target height",
            |log| {
                log.display("target_height", height)
                    .display("currrent_height", &current_height);
            },
        );

        return InUpdateClient::build_update_client_messages(relay, target, height).await;
    }
}
