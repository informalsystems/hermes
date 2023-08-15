use core::marker::PhantomData;

use async_trait::async_trait;

use crate::chain::traits::queries::consensus_state::CanQueryConsensusState;
use crate::chain::traits::types::consensus_state::HasConsensusStateType;
use crate::chain::traits::types::height::HasHeightType;
use crate::chain::types::aliases::Height;
use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::logs::logger::CanLogRelayTarget;
use crate::relay::traits::target::ChainTarget;
use crate::relay::traits::update_client::UpdateClientMessageBuilder;
use crate::std_prelude::*;

pub struct SkipUpdateClient<InUpdateClient>(PhantomData<InUpdateClient>);

#[async_trait]
impl<Relay, Target, InUpdateClient, TargetChain, CounterpartyChain>
    UpdateClientMessageBuilder<Relay, Target> for SkipUpdateClient<InUpdateClient>
where
    Relay: HasRelayChains + CanLogRelayTarget<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    InUpdateClient: UpdateClientMessageBuilder<Relay, Target>,
    CounterpartyChain: HasConsensusStateType<TargetChain> + HasHeightType,
    TargetChain: CanQueryConsensusState<CounterpartyChain>,
{
    async fn build_update_client_messages(
        relay: &Relay,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let target_chain = Target::target_chain(relay);
        let target_client_id = Target::target_client_id(relay);

        let consensus_state = target_chain
            .query_consensus_state(target_client_id, height)
            .await;

        match consensus_state {
            Ok(_) => {
                relay.log_relay_target(
                    Relay::Logger::LEVEL_TRACE,
                    "skip building update client message, as the target chain already has one at given height",
                    |log| {
                        log.display("target_height", height);
                    },
                );

                Ok(Vec::new())
            }
            Err(_) => InUpdateClient::build_update_client_messages(relay, target, height).await,
        }
    }
}
