use async_trait::async_trait;

use crate::chain::traits::client::client_state::CanQueryClientState;
use crate::chain::traits::client::update::{
    CanBuildUpdateClientMessage, CanBuildUpdateClientPayload,
};
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct BuildUpdateClientMessages;

#[async_trait]
impl<Relay, Target, TargetChain, CounterpartyChain> UpdateClientMessageBuilder<Relay, Target>
    for BuildUpdateClientMessages
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    CounterpartyChain: CanBuildUpdateClientPayload<TargetChain>,
    TargetChain:
        CanQueryClientState<CounterpartyChain> + CanBuildUpdateClientMessage<CounterpartyChain>,
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

        let update_payload = counterparty_chain
            .build_update_client_payload(target_height, client_state)
            .await
            .map_err(Target::counterparty_chain_error)?;

        let messages = target_chain
            .build_update_client_message(target_client_id, update_payload)
            .await
            .map_err(Target::target_chain_error)?;

        Ok(messages)
    }
}
