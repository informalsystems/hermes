use async_trait::async_trait;

use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::client::consensus_state::CanFindConsensusStateHeight;
use crate::chain::traits::client::update::{
    CanBuildUpdateClientMessage, CanBuildUpdateClientPayload,
};
use crate::chain::traits::types::client_state::HasClientStateFields;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::relay::traits::update_client::UpdateClientMessageBuilder;
use crate::std_prelude::*;

pub struct BuildUpdateClientMessages;

#[async_trait]
impl<Relay, Target, TargetChain, CounterpartyChain> UpdateClientMessageBuilder<Relay, Target>
    for BuildUpdateClientMessages
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    TargetChain: CanQueryClientState<CounterpartyChain>
        + CanBuildUpdateClientMessage<CounterpartyChain>
        + CanFindConsensusStateHeight<CounterpartyChain>,
    CounterpartyChain: CanBuildUpdateClientPayload<TargetChain> + HasClientStateFields<TargetChain>,
    CounterpartyChain::Height: Clone,
{
    async fn build_update_client_messages(
        relay: &Relay,
        _target: Target,
        target_height: &CounterpartyChain::Height,
    ) -> Result<Vec<TargetChain::Message>, Relay::Error> {
        let target_client_id = Target::target_client_id(relay);

        let target_chain = Target::target_chain(relay);
        let counterparty_chain = Target::counterparty_chain(relay);

        let client_state = target_chain
            .query_client_state(target_client_id)
            .await
            .map_err(Target::target_chain_error)?;

        let client_state_height = CounterpartyChain::client_state_latest_height(&client_state);

        // If the client state height is already the same as target height, then there
        // is no need to build any UpdateClient message
        if client_state_height == target_height {
            return Ok(Vec::new());
        }

        let trusted_height = if client_state_height < target_height {
            // If the client state height is less than the target height, we can use that
            // as a base trust height to build our UpdateClient headers.
            client_state_height.clone()
        } else {
            // If the client state height is greater than the target height, it means we
            // have to find a previous consensus height that is less than the target height.
            let consensus_state_height = target_chain
                .find_consensus_state_height_before(target_client_id, target_height)
                .await
                .map_err(Target::target_chain_error)?;

            // If we happen to find a consensus height that matches the target height,
            // then there is no need to build any UpdateClient message.
            if &consensus_state_height == target_height {
                return Ok(Vec::new());
            }

            consensus_state_height
        };

        let update_payload = counterparty_chain
            .build_update_client_payload(&trusted_height, target_height, client_state)
            .await
            .map_err(Target::counterparty_chain_error)?;

        let messages = target_chain
            .build_update_client_message(target_client_id, update_payload)
            .await
            .map_err(Target::target_chain_error)?;

        Ok(messages)
    }
}
