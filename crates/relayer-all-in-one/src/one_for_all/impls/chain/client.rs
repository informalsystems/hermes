use async_trait::async_trait;
use ibc_relayer_components::chain::traits::client::client_state::CanQueryClientState;
use ibc_relayer_components::chain::traits::client::consensus_state::CanFindConsensusStateHeight;
use ibc_relayer_components::chain::traits::client::create::{
    CanBuildCreateClientMessage, CanBuildCreateClientPayload, HasCreateClientEvent,
    HasCreateClientOptions, HasCreateClientPayload,
};
use ibc_relayer_components::chain::traits::client::update::{
    CanBuildUpdateClientMessage, CanBuildUpdateClientPayload, HasUpdateClientPayload,
};
use ibc_relayer_components::chain::traits::types::client_state::{
    HasClientStateFields, HasClientStateType,
};

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain, Counterparty> HasCreateClientOptions<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type CreateClientPayloadOptions = Chain::CreateClientPayloadOptions;
}

impl<Chain, Counterparty> HasCreateClientPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type CreateClientPayload = Chain::CreateClientPayload;
}

impl<Chain, Counterparty> HasCreateClientEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
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
    Counterparty: OfaChainTypes,
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
    Counterparty: OfaChainTypes,
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

#[async_trait]
impl<Chain, Counterparty> HasClientStateType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type ClientState = Chain::ClientState;
}

#[async_trait]
impl<Chain, Counterparty> HasUpdateClientPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type UpdateClientPayload = Chain::UpdateClientPayload;
}

#[async_trait]
impl<Chain, Counterparty> CanBuildUpdateClientPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_update_client_payload(
        &self,
        trusted_height: &Self::Height,
        target_height: &Self::Height,
        client_state: Self::ClientState,
    ) -> Result<Self::UpdateClientPayload, Self::Error> {
        self.chain
            .build_update_client_payload(trusted_height, target_height, client_state)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildUpdateClientMessage<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_update_client_message(
        &self,
        client_id: &Self::ClientId,
        payload: Counterparty::UpdateClientPayload,
    ) -> Result<Vec<Self::Message>, Self::Error> {
        self.chain
            .build_update_client_message(client_id, payload)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanFindConsensusStateHeight<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn find_consensus_state_height_before(
        &self,
        client_id: &Self::ClientId,
        target_height: &Counterparty::Height,
    ) -> Result<Counterparty::Height, Self::Error> {
        self.chain
            .find_consensus_state_height_before(client_id, target_height)
            .await
    }
}

impl<Chain, Counterparty> HasClientStateFields<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    fn client_state_latest_height(client_state: &Self::ClientState) -> &Self::Height {
        Chain::client_state_latest_height(client_state)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanQueryClientState<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn query_client_state(
        &self,
        client_id: &Self::ClientId,
    ) -> Result<Counterparty::ClientState, Self::Error> {
        self.chain.query_client_state(client_id).await
    }
}
