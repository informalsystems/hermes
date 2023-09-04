use async_trait::async_trait;

use crate::chain::traits::client::create::{
    CanBuildCreateClientMessage, CanBuildCreateClientPayload, HasCreateClientEvent,
    HasCreateClientPayload,
};
use crate::chain::traits::components::message_sender::CanSendSingleMessage;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::create_client::ClientCreator;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct CreateClientWithChains;

pub trait InjectMissingCreateClientEventError<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
{
    fn missing_create_client_event_error(
        target_chain: &Target::TargetChain,
        counterparty_chain: &Target::CounterpartyChain,
    ) -> Self::Error;
}

#[async_trait]
impl<Relay, Target, TargetChain, CounterpartyChain> ClientCreator<Relay, Target>
    for CreateClientWithChains
where
    Relay: InjectMissingCreateClientEventError<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    TargetChain: CanSendSingleMessage
        + CanBuildCreateClientMessage<CounterpartyChain>
        + HasCreateClientEvent<CounterpartyChain>,
    CounterpartyChain:
        CanBuildCreateClientPayload<TargetChain> + HasCreateClientPayload<TargetChain>,
    TargetChain::ClientId: Clone,
{
    async fn create_client(
        target_chain: &TargetChain,
        counterparty_chain: &CounterpartyChain,
        create_client_options: &CounterpartyChain::CreateClientPayloadOptions,
    ) -> Result<TargetChain::ClientId, Relay::Error> {
        let payload = counterparty_chain
            .build_create_client_payload(create_client_options)
            .await
            .map_err(Target::counterparty_chain_error)?;

        let message = target_chain
            .build_create_client_message(payload)
            .await
            .map_err(Target::target_chain_error)?;

        let events = target_chain
            .send_message(message)
            .await
            .map_err(Target::target_chain_error)?;

        let create_client_event = events
            .into_iter()
            .find_map(|event| TargetChain::try_extract_create_client_event(event))
            .ok_or_else(|| {
                Relay::missing_create_client_event_error(target_chain, counterparty_chain)
            })?;

        let client_id = TargetChain::create_client_event_client_id(&create_client_event);

        Ok(client_id.clone())
    }
}
