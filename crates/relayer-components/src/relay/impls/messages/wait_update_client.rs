use async_trait::async_trait;
use core::cmp::Ord;
use core::marker::PhantomData;
use core::time::Duration;

use crate::chain::traits::queries::status::CanQueryChainStatus;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;
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
impl<Relay, Target, InUpdateClient, TargetChain, CounterpartyChain, Height>
    UpdateClientMessageBuilder<Relay, Target> for WaitUpdateClient<InUpdateClient>
where
    Relay: HasRelayTypes,
    Relay: HasRuntime,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    CounterpartyChain: HasIbcChainTypes<TargetChain, Height = Height>,
    TargetChain: HasIbcChainTypes<CounterpartyChain>,
    CounterpartyChain: CanQueryChainStatus,
    Relay::Runtime: CanSleep,
    Height: Ord + Async,
{
    async fn build_update_client_messages(
        context: &Relay,
        target: Target,
        height: &Height,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let chain = Target::counterparty_chain(context);

        loop {
            let current_status = chain
                .query_chain_status()
                .await
                .map_err(Target::counterparty_chain_error)?;

            let current_height = CounterpartyChain::chain_status_height(&current_status);

            if current_height > height {
                return InUpdateClient::build_update_client_messages(context, target, height).await;
            } else {
                context.runtime().sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
