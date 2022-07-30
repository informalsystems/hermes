use async_trait::async_trait;
use core::cmp::Ord;
use core::marker::PhantomData;
use core::time::Duration;

use crate::std_prelude::*;
use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::traits::queries::status::{ChainStatus, ChainStatusQuerierContext};
use crate::traits::relay_context::RelayContext;
use crate::traits::sleep::SleepContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::IbcMessage;

/**
   Wait for the chain to reach a height that is greater than the required height,
   so that the update client proof can be built.
*/
pub struct WaitUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

#[async_trait]
impl<Relay, Target, InUpdateClient, TargetChain, CounterpartyChain, Height, Error>
    UpdateClientMessageBuilder<Relay, Target> for WaitUpdateClient<InUpdateClient>
where
    Relay: RelayContext<Error = Error>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    CounterpartyChain: IbcChainContext<TargetChain, Height = Height, Error = Error>,
    TargetChain: IbcChainContext<CounterpartyChain>,
    CounterpartyChain: ChainStatusQuerierContext,
    CounterpartyChain: SleepContext,
    Height: Ord + Async,
{
    async fn build_update_client_messages(
        context: &Relay,
        height: &Height,
    ) -> Result<Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>, Relay::Error> {
        let chain = Target::counterparty_chain(context);

        loop {
            let current_status = chain.query_chain_status().await?;
            let current_height = current_status.height();

            if current_height > height {
                return InUpdateClient::build_update_client_messages(context, height).await;
            } else {
                CounterpartyChain::sleep(Duration::from_millis(100)).await;
            }
        }
    }
}
