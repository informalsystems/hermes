use async_trait::async_trait;
use core::cmp::Ord;
use core::marker::PhantomData;
use core::time::Duration;

use crate::base::chain::traits::queries::status::CanQueryChainStatus;
use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::std_prelude::*;

/**
   Wait for the chain to reach a height that is greater than the required height,
   so that the update client proof can be built.
*/
pub struct WaitUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

#[async_trait]
impl<Relay, Target, InUpdateClient, TargetChain, CounterpartyChain, Height, Error, Runtime>
    UpdateClientMessageBuilder<Relay, Target> for WaitUpdateClient<InUpdateClient>
where
    Relay: HasRelayTypes<Error = Error>,
    Relay: HasRuntime<Runtime = Runtime>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    CounterpartyChain: HasIbcChainTypes<TargetChain, Height = Height, Error = Error>,
    TargetChain: HasIbcChainTypes<CounterpartyChain>,
    CounterpartyChain: CanQueryChainStatus,
    Runtime: CanSleep,
    Height: Ord + Async,
{
    async fn build_update_client_messages(
        context: &Relay,
        target: Target,
        height: &Height,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let chain = Target::counterparty_chain(context);

        loop {
            let current_status = chain.query_chain_status().await?;
            let current_height = CounterpartyChain::chain_status_height(&current_status);

            if current_height > height {
                return InUpdateClient::build_update_client_messages(context, target, height).await;
            } else {
                context.runtime().sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
