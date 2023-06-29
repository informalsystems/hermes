use crate::one_for_all::traits::chain::OfaIbcChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;
use async_trait::async_trait;
use ibc_relayer_components::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use ibc_relayer_components::chain::traits::types::connection::{
    HasConnectionDetailsType, HasConnectionHandshakePayloads, HasConnectionVersionType,
    HasInitConnectionOptionsType,
};
use ibc_relayer_components::chain::traits::types::ibc_events::connection::HasConnectionOpenInitEvent;

impl<Chain, Counterparty> HasConnectionHandshakePayloads<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConnectionOpenInitPayload = Chain::ConnectionOpenInitPayload;

    type ConnectionOpenTryPayload = Chain::ConnectionOpenTryPayload;

    type ConnectionOpenAckPayload = Chain::ConnectionOpenAckPayload;

    type ConnectionOpenConfirmPayload = Chain::ConnectionOpenConfirmPayload;
}

impl<Chain, Counterparty> HasInitConnectionOptionsType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type InitConnectionOptions = Chain::InitConnectionOptions;
}

impl<Chain, Counterparty> HasConnectionVersionType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConnectionVersion = Chain::ConnectionVersion;
}

impl<Chain, Counterparty> HasConnectionDetailsType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConnectionDetails = Chain::ConnectionDetails;
}

impl<Chain, Counterparty> HasConnectionOpenInitEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConnectionOpenInitEvent = Chain::ConnectionOpenInitEvent;

    fn try_extract_connection_open_init_event(
        event: Chain::Event,
    ) -> Option<Chain::ConnectionOpenInitEvent> {
        Chain::try_extract_connection_open_init_event(event)
    }

    fn connection_open_init_event_connection_id(
        event: &Chain::ConnectionOpenInitEvent,
    ) -> &Chain::ConnectionId {
        Chain::connection_open_init_event_connection_id(event)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildConnectionHandshakePayloads<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn build_connection_open_init_payload(
        &self,
    ) -> Result<Self::ConnectionOpenInitPayload, Self::Error> {
        self.chain.build_connection_open_init_payload().await
    }

    async fn build_connection_open_try_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenTryPayload, Self::Error> {
        self.chain
            .build_connection_open_try_payload(height, client_id, connection_id)
            .await
    }

    async fn build_connection_open_ack_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenAckPayload, Self::Error> {
        self.chain
            .build_connection_open_ack_payload(height, client_id, connection_id)
            .await
    }

    async fn build_connection_open_confirm_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenConfirmPayload, Self::Error> {
        self.chain
            .build_connection_open_confirm_payload(height, client_id, connection_id)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildConnectionHandshakeMessages<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn build_connection_open_init_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        init_connection_options: &Self::InitConnectionOptions,
        counterparty_payload: Counterparty::ConnectionOpenInitPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_connection_open_init_message(
                client_id,
                counterparty_client_id,
                init_connection_options,
                counterparty_payload,
            )
            .await
    }

    async fn build_connection_open_try_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        counterparty_connection_id: &Counterparty::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenTryPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_connection_open_try_message(
                client_id,
                counterparty_client_id,
                counterparty_connection_id,
                counterparty_payload,
            )
            .await
    }

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_connection_id: &Counterparty::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenAckPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_connection_open_ack_message(
                connection_id,
                counterparty_connection_id,
                counterparty_payload,
            )
            .await
    }

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenConfirmPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_connection_open_confirm_message(connection_id, counterparty_payload)
            .await
    }
}
