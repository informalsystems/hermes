use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::error::HasErrorType;
use crate::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasCreateClientOptions<Counterparty>: HasIbcChainTypes<Counterparty> {
    type CreateClientPayloadOptions: Async;
}

pub trait HasCreateClientPayload<Counterparty>: HasIbcChainTypes<Counterparty> {
    type CreateClientPayload: Async;
}

pub trait HasCreateClientEvent<Counterparty>: HasIbcChainTypes<Counterparty> {
    type CreateClientEvent: Async;

    fn try_extract_create_client_event(event: Self::Event) -> Option<Self::CreateClientEvent>;

    fn create_client_event_client_id(event: &Self::CreateClientEvent) -> &Self::ClientId;
}

#[async_trait]
pub trait CanBuildCreateClientPayload<Counterparty>:
    HasCreateClientOptions<Counterparty> + HasCreateClientPayload<Counterparty> + HasErrorType
{
    async fn build_create_client_payload(
        &self,
        create_client_options: &Self::CreateClientPayloadOptions,
    ) -> Result<Self::CreateClientPayload, Self::Error>;
}

#[async_trait]
pub trait CanBuildCreateClientMessage<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasErrorType
where
    Counterparty: HasCreateClientPayload<Self>,
{
    async fn build_create_client_message(
        &self,
        counterparty_payload: Counterparty::CreateClientPayload,
    ) -> Result<Self::Message, Self::Error>;
}
