use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::base::traits::queries::consensus_state::{HasConsensusState, HasConsensusStateQuerier};
use crate::base::traits::target::ChainTarget;
use crate::base::types::aliases::Height;
use crate::std_prelude::*;

pub struct SkipUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

#[async_trait]
impl<Relay, Target, InUpdateClient, TargetChain, CounterpartyChain>
    UpdateClientMessageBuilder<Relay, Target> for SkipUpdateClient<InUpdateClient>
where
    Relay: RelayContext,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    CounterpartyChain: HasConsensusState<TargetChain>,
    TargetChain: HasConsensusStateQuerier<CounterpartyChain>,
{
    async fn build_update_client_messages(
        context: &Relay,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let target_chain = Target::target_chain(context);
        let target_client_id = Target::target_client_id(context);

        let consensus_state = target_chain
            .query_consensus_state(target_client_id, height)
            .await;

        match consensus_state {
            Ok(_) => Ok(Vec::new()),
            Err(_) => InUpdateClient::build_update_client_messages(context, height).await,
        }
    }
}
