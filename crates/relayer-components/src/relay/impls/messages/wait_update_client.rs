use core::marker::PhantomData;
use core::time::Duration;

use async_trait::async_trait;

use crate::chain::traits::queries::status::CanQueryChainStatus;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::traits::logs::logger::CanLogRelayTarget;
use crate::relay::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::relay::traits::target::ChainTarget;
use crate::relay::traits::types::HasRelayTypes;
use crate::runtime::traits::runtime::HasRuntime;
use crate::runtime::traits::sleep::CanSleep;
use crate::std_prelude::*;

/**
   Wait for the chain to reach a height that is greater than the required height,
   so that the update client proof can be built.
*/
pub struct WaitUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

#[async_trait]
impl<Relay, Target, InUpdateClient, TargetChain, CounterpartyChain>
    UpdateClientMessageBuilder<Relay, Target> for WaitUpdateClient<InUpdateClient>
where
    Relay: HasRelayTypes + HasRuntime + CanLogRelayTarget<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    CounterpartyChain: HasIbcChainTypes<TargetChain>,
    TargetChain: HasIbcChainTypes<CounterpartyChain>,
    CounterpartyChain: CanQueryChainStatus,
    Relay::Runtime: CanSleep,
{
    async fn build_update_client_messages(
        relay: &Relay,
        target: Target,
        height: &CounterpartyChain::Height,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let chain = Target::counterparty_chain(relay);

        relay.log_relay_target(
            Relay::Logger::LEVEL_TRACE,
            "waiting for counterparty chain to reach height",
            |log| {
                log.display("target_height", height);
            },
        );

        loop {
            let current_status = chain
                .query_chain_status()
                .await
                .map_err(Target::counterparty_chain_error)?;

            let current_height = CounterpartyChain::chain_status_height(&current_status);

            if current_height > height {
                relay.log_relay_target(
                    Relay::Logger::LEVEL_TRACE,
                    "counterparty chain's height is now greater than target height",
                    |log| {
                        log.display("target_height", height)
                            .display("currrent_height", &current_height);
                    },
                );

                return InUpdateClient::build_update_client_messages(relay, target, height).await;
            } else {
                relay.runtime().sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
