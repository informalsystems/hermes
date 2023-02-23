use async_trait::async_trait;
use core::marker::PhantomData;

use crate::chain::traits::queries::consensus_state::CanQueryConsensusState;
use crate::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::chain::types::aliases::Height;
use crate::relay::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::relay::traits::target::ChainTarget;
use crate::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct SkipUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

#[async_trait]
impl<Relay, Target, InUpdateClient, TargetChain, CounterpartyChain>
    UpdateClientMessageBuilder<Relay, Target> for SkipUpdateClient<InUpdateClient>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    CounterpartyChain: HasConsensusStateType<TargetChain>,
    TargetChain: CanQueryConsensusState<CounterpartyChain>,
{
    async fn build_update_client_messages(
        context: &Relay,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let target_chain = Target::target_chain(context);
        let target_client_id = Target::target_client_id(context);

        let consensus_state = target_chain
            .query_consensus_state(target_client_id, height)
            .await;

        match consensus_state {
            Ok(_) => Ok(Vec::new()),
            Err(_) => InUpdateClient::build_update_client_messages(context, target, height).await,
        }
    }
}
