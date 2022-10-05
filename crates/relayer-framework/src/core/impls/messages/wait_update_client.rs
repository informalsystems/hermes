use async_trait::async_trait;
use core::cmp::Ord;
use core::marker::PhantomData;
use core::time::Duration;

use crate::core::traits::contexts::chain::IbcChainContext;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::core::traits::queries::status::HasChainStatusQuerier;
use crate::core::traits::runtime::sleep::CanSleep;
use crate::core::traits::target::ChainTarget;
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
    Relay: RelayContext<Error = Error, Runtime = Runtime>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    CounterpartyChain: IbcChainContext<TargetChain, Height = Height, Error = Error>,
    TargetChain: IbcChainContext<CounterpartyChain>,
    CounterpartyChain: HasChainStatusQuerier,
    Runtime: CanSleep,
    Height: Ord + Async,
{
    async fn build_update_client_messages(
        context: &Relay,
        height: &Height,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let chain = Target::counterparty_chain(context);

        loop {
            let current_status = chain.query_chain_status().await?;
            let current_height = CounterpartyChain::chain_status_height(&current_status);

            if current_height > height {
                return InUpdateClient::build_update_client_messages(context, height).await;
            } else {
                context.runtime().sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
