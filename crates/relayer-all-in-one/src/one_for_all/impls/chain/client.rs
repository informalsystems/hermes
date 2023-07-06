use async_trait::async_trait;
use ibc_relayer_components::chain::traits::client::create::{
    CanBuildCreateClientMessage, CanBuildCreateClientPayload, HasCreateClientEvent,
    HasCreateClientOptions, HasCreateClientPayload,
};

use crate::one_for_all::traits::chain::OfaIbcChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain, Counterparty> HasCreateClientOptions<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type CreateClientPayloadOptions = Chain::CreateClientPayloadOptions;
}

impl<Chain, Counterparty> HasCreateClientPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type CreateClientPayload = Chain::CreateClientPayload;
}

impl<Chain, Counterparty> HasCreateClientEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type CreateClientEvent = Chain::CreateClientEvent;

    fn try_extract_create_client_event(event: Self::Event) -> Option<Self::CreateClientEvent> {
        Chain::try_extract_create_client_event(event)
    }

    fn create_client_event_client_id(event: &Self::CreateClientEvent) -> &Self::ClientId {
        Chain::create_client_event_client_id(event)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildCreateClientPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn build_create_client_payload(
        &self,
        create_client_options: &Self::CreateClientPayloadOptions,
    ) -> Result<Self::CreateClientPayload, Self::Error> {
        self.chain
            .build_create_client_payload(create_client_options)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildCreateClientMessage<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn build_create_client_message(
        &self,
        counterparty_payload: Counterparty::CreateClientPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_create_client_message(counterparty_payload)
            .await
    }
}
