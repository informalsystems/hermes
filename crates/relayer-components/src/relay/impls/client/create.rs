use async_trait::async_trait;

use crate::chain::traits::client::create::{
    CanBuildCreateClientMessage, CanBuildCreateClientPayload, HasCreateClientEvent,
    HasCreateClientOptionsType, HasCreateClientPayloadType,
};
use crate::chain::traits::message_sender::CanSendSingleMessage;
use crate::chain::types::aliases::ClientId;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub trait InjectMissingCreateClientEventError<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
{
    fn missing_create_client_event(
        target_chain: &Target::TargetChain,
        counterparty_chain: &Target::CounterpartyChain,
    ) -> Self::Error;
}

#[async_trait]
pub trait CanCreateClient<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::CounterpartyChain: HasCreateClientOptionsType<Target::TargetChain>,
{
    /**
       Create a new IBC client on the target chain.

       Notice that this function does not take in `&self` as argument.
       This is because the relay context is required to have fixed client IDs already.
       Since the relay context can't be built yet without the client IDs,
       we pass in the target and counterparty chains as argument directly.

       We define this as a static method for the relay context to reuse the
       existing infrastructure, particularly in handling errors from two chains
       which may be of different types.
    */
    async fn create_client(
        target_chain: &Target::TargetChain,
        counterparty_chain: &Target::CounterpartyChain,
        create_client_options: &<Target::CounterpartyChain as HasCreateClientOptionsType<
            Target::TargetChain,
        >>::CreateClientOptions,
    ) -> Result<ClientId<Target::TargetChain, Target::CounterpartyChain>, Self::Error>;
}

#[async_trait]
impl<Relay, Target, TargetChain, CounterpartyChain> CanCreateClient<Target> for Relay
where
    Relay: InjectMissingCreateClientEventError<Target>,
    Target: ChainTarget<Self, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    TargetChain: CanSendSingleMessage
        + CanBuildCreateClientMessage<CounterpartyChain>
        + HasCreateClientEvent<CounterpartyChain>,
    CounterpartyChain:
        CanBuildCreateClientPayload<TargetChain> + HasCreateClientPayloadType<TargetChain>,
    TargetChain::ClientId: Clone,
{
    async fn create_client(
        target_chain: &TargetChain,
        counterparty_chain: &CounterpartyChain,
        create_client_options: &CounterpartyChain::CreateClientOptions,
    ) -> Result<TargetChain::ClientId, Self::Error> {
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
            .ok_or_else(|| Relay::missing_create_client_event(target_chain, counterparty_chain))?;

        let client_id = TargetChain::create_client_event_client_id(&create_client_event);

        Ok(client_id.clone())
    }
}
